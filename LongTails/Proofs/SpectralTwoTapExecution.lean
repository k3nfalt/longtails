import LongTails.Algorithms.SpectralTwoTapGd
import LongTails.Proofs.SpectralTwoTapSeparation
import LongTails.Proofs.Execution

open OracleTemplate
open LongTails.Setups.SpectralTwoTapLogistic
open LongTails.Algorithms.SpectralTwoTapGd
open LongTails.Proofs.SpectralTwoTapSeparation

namespace LongTails.Proofs.SpectralTwoTapExecution

lemma allowed (p : Params) (hp : valid p) :
    spec.allowedAlgorithm p.input (algorithm p.input) := by
  exact ⟨p.input.η,id,hp.1,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,fun _ => rfl⟩

lemma succeeds (p : Params) (hp : valid p) (D : Images p.input)
    (O : Oracle (State p.input.d) (State p.input.d)) (had : spec.admissible p D O)
    (seed : (algorithm p.input).Seed) (ξ : ∀ i, O.Seed i) :
    correct D (execute O (algorithm p.input) (fun _ => p.K+2*⌈2*p.d/p.W⌉₊) seed ξ) := by
  obtain ⟨hg,ha⟩ := had
  let gd := algorithm p.input
  let z (k : ℕ) : State p.input.d := (fun t => gd.update t (descent D (gd.query t).2))^[k] (gd.initial seed)
  have step (k : ℕ) : z (k+1) = z k + p.input.η • descent D (z k) := by
    dsimp only [z]
    rw [Function.iterate_succ_apply']
    rfl
  rw [execute_eq_of_answer_eq O (descent D) (fun k q ω => ha k (0,q) ω),execute_iterate]
  exact separates p hp D hg z rfl step

end LongTails.Proofs.SpectralTwoTapExecution
