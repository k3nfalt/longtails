import LongTails.Algorithms.BirchNonEuclideanRennala

namespace LongTails.Algorithms.BirchNonEuclideanRennalaProtocols

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanRennala

noncomputable def publicFamily {m : ℕ} (events : ℕ → ℕ → List (Event m)) : ProtocolFamily where
  template := fun K B => makeTemplate K (eventsCode K B (events K B))

def publicCalls {m : ℕ} (events : ℕ → ℕ → List (Event m)) (K B : ℕ) : ℕ :=
  (run K B (events K B)).queries.length

end LongTails.Algorithms.BirchNonEuclideanRennalaProtocols
