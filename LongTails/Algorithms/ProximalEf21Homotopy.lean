import LongTails.Setups.StochasticProximalEf21

open MeasureTheory

noncomputable section

namespace LongTails.Algorithms.ProximalEf21Homotopy

open OracleTemplate
open LongTails.Setups.StochasticProximalEf21

noncomputable def make (p : Public) :
    Algorithm (Query p) (Reply p) (Output p) 4 := method p

noncomputable def output (p : Public)
    (O : Oracle (Query p) (Reply p) 4)
    (budget : Fin 4 → ℕ)
    (initial : InitialMemories p)
    (seeds : (k : ℕ) → O.Seed k) : Point p :=
  (execute O (make p) budget initial seeds).1

noncomputable def outputWithCounts (p : Public)
    (O : Oracle (Query p) (Reply p) 4)
    (budget : Fin 4 → ℕ)
    (initial : InitialMemories p)
    (seeds : (k : ℕ) → O.Seed k) : Output p :=
  execute O (make p) budget initial seeds

end LongTails.Algorithms.ProximalEf21Homotopy
