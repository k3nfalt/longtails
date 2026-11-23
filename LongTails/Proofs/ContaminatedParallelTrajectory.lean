import LongTails.Algorithms.ContaminatedParallelDescent
import LongTails.Proofs.LeonRoundTrace
import LongTails.Proofs.LeonEstimator

namespace LongTails.Proofs.ContaminatedParallelTrajectory

open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms
open LeonTranscript

structure Round (p : Params) where
  op : Operation
  model : Model p
  values : Fin p.n → List (Point p)

variable {p : Params}

noncomputable def codes (r : Round p) (i : Fin p.n) :=
  LeonAggregate.localCodes (LeonTuning.spacing (network p)) (reference p r.model r.op)
    (estimate p (r.op.precision p) i (r.values i))

noncomputable def rawCodes (r : Round p) (j : Fin p.d) : ℤ := ∑ i, codes r i j

noncomputable def decoded (r : Round p) : Point p :=
  Algorithms.LeonAggregate.decode p.n (LeonTuning.width (network p) r.op.level)
    (LeonTuning.spacing (network p)) (LeonTuning.radius (network p) r.op.level)
    (reference p r.model r.op) (rawCodes r)

noncomputable def scatter (r : Round p) (i j : Fin p.n) :=
  Algorithms.LeonExchange.scatter (network p) r.op.level j (codes r i)

noncomputable def gather (r : Round p) (i : Fin p.n) :=
  Algorithms.LeonExchange.gather (network p) r.op.level (fun j => wire (scatter r j i))

noncomputable def actions (r : Round p) (i : Fin p.n) : List (Op (network p)) :=
  .sample (location p r.model r.op, batch p (r.op.precision p) i) (r.values i) ::
    (exchangeOps (network p) (scatter r i) (fun j => wire (scatter r j i)) ++
     exchangeOps (network p) (fun _ => gather r i) (fun j => wire (gather r j)))

lemma round_trace (r : Round p) (i : Fin p.n) (ls : List Operation)
    (rest : List (Op (network p))) (x : Point p)
    (h : Trace (schedule p i ls (advance p r.model r.op (decoded r))) rest x) :
    Trace (schedule p i (r.op :: ls) r.model) (actions r i ++ rest) x := by
  simp only [schedule, aggregate, actions, List.cons_append, List.append_assoc]
  apply Trace.sample
  apply exchange_trace
  apply exchange_trace
  have he (j : Fin p.d) :=
    Proofs.LeonExchange.round_trip (network p) r.op.level (codes r) (fun _ _ => List.replicate DistributedTemplate.clockBits false)
      (fun _ => List.replicate DistributedTemplate.clockBits false) j
  have hv : (fun j => DashaModular.restore (LeonTuning.width (network p) r.op.level)
      (Algorithms.LeonExchange.unpack (network p) r.op.level (fun j => wire (gather r j)) j)) =
      fun j => DashaModular.restore (LeonTuning.width (network p) r.op.level) (rawCodes r j) := by
    funext j
    rw [show Algorithms.LeonExchange.unpack (network p) r.op.level (fun j => wire (gather r j)) j =
      rawCodes r j % DashaModular.modulus (LeonTuning.width (network p) r.op.level) from he j,
      Proofs.DashaModular.restore_mod]
  let finish (v : Fin p.d → ℤ) : Prop := Trace (schedule p i ls (advance p r.model r.op
    (let d := Algorithms.LeonAggregate.displacement p.n (LeonTuning.spacing (network p)) v
     if ‖d‖ ≤ LeonTuning.radius (network p) r.op.level then reference p r.model r.op + d
     else reference p r.model r.op))) rest x
  exact (congrArg finish hv).mpr h

noncomputable def read (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (samples : Samples p)
    (u : Fin p.n → ℕ) (m : Model p) (op : Operation) : Round p :=
  ⟨op, m, fun i => (List.range (batch p (op.precision p) i)).map
    (fun j => g i (location p m op) (samples i (u i+j)))⟩

noncomputable def nextOffset (p : Params) (u : Fin p.n → ℕ) (op : Operation) (i : Fin p.n) :=
  u i + (batch p (op.precision p) i : ℕ)

noncomputable def trajectory (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) : List Operation → (Fin p.n → ℕ) → Model p → Model p
  | [], _, m => m
  | op :: rest, u, m => trajectory p g samples rest (nextOffset p u op)
      (advance p m op (decoded (read p g samples u m op)))

noncomputable def offset (p : Params) (ls : List Operation) (u : Fin p.n → ℕ) : Fin p.n → ℕ :=
  ls.foldl (nextOffset p) u

lemma trajectory_append (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)
    (ls rest : List Operation) (u : Fin p.n → ℕ) (m : Model p) :
    trajectory p g s (ls ++ rest) u m =
      trajectory p g s rest (offset p ls u) (trajectory p g s ls u m) := by
  induction ls generalizing u m with
  | nil => rfl
  | cons op ls ih => exact ih _ _

end LongTails.Proofs.ContaminatedParallelTrajectory
