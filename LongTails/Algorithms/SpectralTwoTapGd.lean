import LongTails.Setups.SpectralTwoTapLogistic

open OracleTemplate

namespace LongTails.Algorithms.SpectralTwoTapGd

open LongTails.Setups.SpectralTwoTapLogistic

noncomputable def algorithm (u : Input) : Algorithm (State u.d) (State u.d) (State u.d) where
  State := State u.d
  initial _ := u.start
  query s := (0,s)
  update s r := s + u.η • r
  output := id

end LongTails.Algorithms.SpectralTwoTapGd
