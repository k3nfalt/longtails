import LongTails.Algorithms.DistributedBatchedSgd

namespace LongTails.Tests.DistributedBatchedSgd

open DistributedTemplate
open LongTails.Setups.DistributedSmoothNonconvex
open LongTails.Algorithms.DistributedBatchedSgd

example (p : Params) (cfg : Config p) (s : State p) (i j : Fin p.n) (bits : List Bool) :
    let start := { s with outbox := some bits, targets := [i, j] }
    let first := (algorithm p cfg).query 0 start 0
    let second := (algorithm p cfg).query 0 first.2 0
    first.1 = .communicate (i.succ, bits) ∧
      second.1 = .communicate (j.succ, bits) ∧
      second.2.targets = [] ∧ second.2.outbox = none ∧
      ((algorithm p cfg).query 0 second.2 0).1 = .advance 0 := by
  simp [algorithm]

example (p : Params) (cfg : Config p) : timeBudget p cfg < (algorithm p cfg).timer 0 := by
  exact lt_add_of_pos_right _ zero_lt_one

end LongTails.Tests.DistributedBatchedSgd
