import LongTails.TemplateDistributed
import Mathlib.Data.List.MinMax

open MeasureTheory

namespace LongTails.Setups.StarNetwork

open DistributedTemplate

structure Network (n : ℕ) where
  computeTime : Fin n → Time
  latency : Time
  timePerBit : Time

inductive ComputeQuery (Input : Type)
  | evaluate (input : Input)
  | abort

inductive ComputeReply (Input Output : Type)
  | computed (input : Input) (output : Output)

inductive CommReply (n : ℕ)
  | received (source : Fin (n + 1)) (bits : List Bool)

structure ComputationState (Input Seed : Type) where
  pending : Option (Time × Input)
  seed : Seed
  used : ℕ

structure CommunicationState (n : ℕ) where
  messages : Fin (n + 1) → Fin (n + 1) → Option (Time × List Bool)

variable {Input Output Seed : Type} {n : ℕ}

noncomputable def computation (N : Network n)
    (compute : Fin n → Input → Seed → ℕ → Output) :
    ComputationOracle (ComputeQuery Input) (ComputeReply Input Output) Seed (n + 1) where
  State := ComputationState Input Seed
  initial _ seed := ⟨none, seed, 0⟩
  submit v s time query :=
    match query with
    | .evaluate input =>
        Fin.cases s (fun i =>
          match s.pending with
          | some _ => s
          | none => { s with pending := some (time + N.computeTime i, input) }) v
    | .abort => { s with pending := none }
  answer v s time :=
    Fin.cases none (fun i =>
      match s.pending with
      | none => none
      | some (finish, input) =>
          if finish ≤ time then
            some (.computed input (compute i input s.seed s.used),
              { s with pending := none, used := s.used + 1 })
          else none) v

noncomputable def communication (N : Network n) :
    CommunicationOracle (CommReply n) Seed (n + 1) where
  State := CommunicationState n
  initial _ := ⟨fun _ _ => none⟩
  submit s time source query :=
    let (target, bits) := query
    if (source = 0 ∧ target ≠ 0) ∨ (source ≠ 0 ∧ target = 0) then
      match s.messages source target with
      | some _ => s
      | none =>
          let finish := time + N.timePerBit * bits.length + N.latency
          { s with messages := (Function.update s.messages source
              (Function.update (s.messages source) target (some (finish, bits)))) }
    else s
  answer s time :=
    let messages := (List.finRange (n + 1)).flatMap fun source =>
      (List.finRange (n + 1)).filterMap fun target =>
        (s.messages source target).map fun (finish, bits) => (finish, source, target, bits)
    match List.argmin Prod.fst messages with
    | none => none
    | some (finish, source, target, bits) =>
        if finish ≤ time then
          some ((target, .received source bits),
            { s with
              messages :=
                Function.update s.messages source (Function.update (s.messages source) target none) })
        else none

noncomputable def system [MeasurableSpace Seed] (N : Network n)
    (compute : Fin n → Input → Seed → ℕ → Output) (P : ProbabilityMeasure Seed) :
    Oracle (ComputeQuery Input) (ComputeReply Input Output) (CommReply n) (n + 1) where
  Seed := Seed
  law := P
  computation := computation N compute
  communication := communication N

end LongTails.Setups.StarNetwork
