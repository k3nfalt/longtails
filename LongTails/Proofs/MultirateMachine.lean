import LongTails.Proofs.MultirateReservations
import LongTails.Proofs.DistributedExecution

open MeasureTheory

namespace LongTails.Proofs.MultirateMachine

open DistributedTemplate
open LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Setups.StarNetwork
open LongTails.Algorithms.MultirateTrajectory LongTails.Algorithms.MultirateProtocol
open LongTails.Algorithms.MultirateCalendar LongTails.Algorithms.MultirateAllocation
open MultirateReservations

variable {p : Params}

inductive Cell (p : Params)
  | free (e : ℕ)
  | down (job : Job p) (atTime : Time)
  | dispatch (job : Job p) (used : ℕ) (atTime : Time)
  | work (job : Job p) (used : ℕ) (atTime : Time)
  | up (job : Job p) (atTime : Time)
  | buffered (job : Job p)

abbrev Table (p : Params) := Fin p.n → Cell p

def booking : Cell p → Reservation p
  | .free e => .free e
  | .down a _ | .dispatch a _ _ | .work a _ _ | .up a _ | .buffered a => .pending a

noncomputable def downlink : Cell p → Option (Time × List Bool)
  | .down a t => some (t, wire a.query)
  | _ => none

noncomputable def uplink (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (i : Fin p.n) :
    Cell p → Option (Time × List Bool)
  | .up a t => some (t, jobReply g s i a)
  | _ => none

noncomputable def mailbox (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (i : Fin p.n) :
    Cell p → Option (List Bool)
  | .buffered a => some (jobReply g s i a)
  | _ => none

noncomputable def phaseOf (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (i : Fin p.n) :
    Cell p → Phase p
  | .dispatch a j _ => .batch (jobInput p a) j (partialSum g s i a j) false
  | .work a j _ => .batch (jobInput p a) j (partialSum g s i a j) true
  | _ => .idle

noncomputable def computationOf (s : Samples p) (i : Fin p.n) : Cell p → ComputationState (Point p) (Samples p)
  | .free e => ⟨none,s,e * batch p i⟩
  | .down a _ => ⟨none,s,a.number * batch p i⟩
  | .dispatch a j _ => ⟨none,s,a.number * batch p i + j⟩
  | .work a j t => ⟨some (t,jobInput p a),s,a.number * batch p i + j⟩
  | .up a _ | .buffered a => ⟨none,s,(a.number+1) * batch p i⟩

noncomputable def busy (p : Params) (i : Fin p.n) : Cell p → ℕ
  | .down _ _ => 2 * batch p i + 3
  | .dispatch _ j _ => 2 * (batch p i - j) + 2
  | .work _ j _ => 2 * (batch p i - j) + 1
  | .up _ _ => 1
  | _ => 0

def readyTime : Cell p → Option Time
  | .down _ t | .dispatch _ _ t | .work _ _ t | .up _ t => some t
  | _ => none

noncomputable def Feasible (p : Params) (i : Fin p.n) : Cell p → Prop
  | .free _ | .buffered _ => True
  | .down a t => t ≤ a.posted + packetDelay p
  | .dispatch a j t => j ≤ batch p i ∧ t ≤ a.posted + packetDelay p + j * p.h i
  | .work a j t => j < batch p i ∧ t ≤ a.posted + packetDelay p + (j+1 : ℕ) * p.h i
  | .up a t => t ≤ a.posted + span p i

lemma ready_before {i : Fin p.n} {c : Cell p} {a : Job p} {t : Time}
    (hb : booking c = .pending a) (hc : Feasible p i c) (ht : readyTime c = some t) :
    t ≤ a.posted + span p i := by
  cases c with
  | free | buffered => cases ht
  | down b u =>
    cases hb; cases ht
    exact hc.trans (by unfold span; simp only [add_assoc]; exact add_le_add_right (le_add_of_nonneg_right zero_le) _)
  | dispatch b j u =>
    cases hb; cases ht
    obtain ⟨hj, hu⟩ := hc
    apply hu.trans
    unfold span
    calc
      _ ≤ a.posted + packetDelay p + (batch p i : Time)*p.h i :=
        add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) zero_le) _
      _ ≤ _ := by simp [add_assoc]
  | work b j u =>
    cases hb; cases ht
    obtain ⟨hj, hu⟩ := hc
    apply hu.trans
    unfold span
    have hv := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj : ((j+1 : ℕ) : Time) ≤ batch p i) (show (0 : Time) ≤ p.h i from zero_le)
    calc
      _ ≤ a.posted + packetDelay p + (batch p i : Time)*p.h i := add_le_add_right hv _
      _ ≤ _ := by simp [add_assoc]
  | up b u => cases hb; cases ht; exact hc

noncomputable abbrev network (p : Params) : Network p.n := ⟨p.h,p.l,p.b⟩
noncomputable abbrev evalAt (g : Fin p.n → Point p → p.Ω → Point p) :=
  fun i x (s : Samples p) k => g i x (s i k)
noncomputable abbrev systemOf (g : Fin p.n → Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p)) :=
  Setups.DistributedAggregateSmoothNonconvex.system (aggregate p) g P

noncomputable def messages (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (b : Table p) :
    Fin (p.n+1) → Fin (p.n+1) → Option (Time × List Bool) := Fin.cases
  (Fin.cases none fun i => downlink (b i))
  fun i => Fin.cases (uplink g s i (b i)) (fun _ => none)

noncomputable def oracleOf (g : Fin p.n → Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p))
    (s : Samples p) (b : Table p) : OracleState (systemOf g P) :=
  ⟨Fin.cases ⟨none,s,0⟩ (fun i => computationOf s i (b i)), ⟨messages g s b⟩⟩

noncomputable def inbox (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (b : Table p) :=
  fun i => mailbox g s i (b i)

noncomputable def workersOf (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)
    (b : Table p) (prog : Program p) : Fin (p.n+1) → State p :=
  Fin.cases ⟨prog, inbox g s b, .idle, false⟩ (fun i => ⟨.done p.x0,fun _ => none,phaseOf g s i (b i),false⟩)

lemma wire_delay {bits : List Bool} (hb : bits.length = payload p) (t : Time) :
    t + p.b * (wire bits).length + p.l = t + packetDelay p := by
  simp only [wire, List.length_append, List.length_replicate, hb, packetDelay, payload]
  ac_rfl

lemma feasible_work {a : Job p} {t : Time} {i : Fin p.n} (h : Feasible p i (.down a t)) :
    Feasible p i (.work a 0 (t + p.h i)) := by
  refine ⟨MultirateAllocation.batch_pos i, ?_⟩
  simpa using add_le_add_right h (p.h i)

lemma feasible_next {a : Job p} {t : Time} {i : Fin p.n} {j : ℕ}
    (h : Feasible p i (.work a j t)) (hj : j+1 < batch p i) :
    Feasible p i (.work a (j+1) (t + p.h i)) := by
  refine ⟨hj, ?_⟩
  have ht := add_le_add_right h.2 (p.h i)
  simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc, add_left_comm, add_comm] using ht

lemma feasible_reply {a : Job p} {t : Time} {i : Fin p.n} {j : ℕ}
    (h : Feasible p i (.work a j t)) (hj : ¬j+1 < batch p i) :
    Feasible p i (.up a (t + packetDelay p)) := by
  obtain ⟨hlt,ht⟩ := h
  have he : j+1 = batch p i := by omega
  rw [he] at ht
  change t + packetDelay p ≤ a.posted + span p i
  simpa [span, add_assoc, add_comm, add_left_comm] using add_le_add_right ht (packetDelay p)

end LongTails.Proofs.MultirateMachine
