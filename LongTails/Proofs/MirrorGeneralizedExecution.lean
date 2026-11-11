import LongTails.Proofs.Execution
import LongTails.Proofs.MirrorGeneralizedRun

namespace LongTails.Proofs.MirrorGeneralizedExecution

open OracleTemplate LongTails.Setups.MirrorGeneralizedSmooth
open LongTails.Algorithms.MirrorGeneralizedAcceleration

noncomputable def response {p : Public} (I : Instance p) : Query p → Reply p
  | .gradient x => .gradient (I.grad x)
  | .prox z v => .prox (I.prox z v)

lemma execute_exact {p : Public} (I : Instance p) (N : ℕ) :
    execute { answer := fun _ q _ => response I q.2 } (algorithm p) (fun _ => 3 * N) =
      (run p I.grad I.prox N).x := by
  let A := algorithm p
  let T := fun s => A.update s (response I (A.query s).2)
  have hi : ∀ n, T^[3 * n] (A.initial ()) = State.pilot (run p I.grad I.prox n) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [show 3 * (n + 1) = ((3 * n + 1) + 1) + 1 by ring,
        Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih]
      rfl
  have he := execute_iterate (response I) (algorithm p) (3 * N) ()
  refine he.trans ?_
  change A.output (T^[3 * N] (A.initial ())) = _
  rw [hi]
  rfl

lemma execute_oracle {p : Public} (I : Instance p) (oracle : Oracle (Query p) (Reply p))
    (hg : ∀ history seed x, oracle.answer history (0, .gradient x) seed = .gradient (I.grad x))
    (hp : ∀ history seed z v, oracle.answer history (0, .prox z v) seed = .prox (I.prox z v))
    (N : ℕ) (seed : (algorithm p).Seed) (ξ : (k : ℕ) → oracle.Seed k) :
    execute oracle (algorithm p) (fun _ => 3 * N) seed ξ = (run p I.grad I.prox N).x := by
  have he := execute_eq_of_answer_eq oracle (response I) (by
    intro history q seed
    cases q with
    | gradient x => exact hg history seed x
    | prox z v => exact hp history seed z v) (algorithm p) (3 * N) seed ξ
  let : Subsingleton (algorithm p).Seed := by
    change Subsingleton Unit
    infer_instance
  have hs : seed = (show (algorithm p).Seed from ()) := Subsingleton.elim _ _
  rw [hs] at he
  exact he.trans (execute_exact I N)

end LongTails.Proofs.MirrorGeneralizedExecution
