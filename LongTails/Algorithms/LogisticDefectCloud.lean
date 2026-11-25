import LongTails.Setups.LogisticDefectCloud

open MeasureTheory ProbabilityTheory OracleTemplate
open LongTails.Setups.LogisticDefectCloud

namespace LongTails.Algorithms.LogisticDefectCloud

def output {p : Params} (s : Scan p) : Weights p.d := s.point

noncomputable def algorithm (p : Params) (η : ℝ) :
    Algorithm (Query p) (Reply p.d) (Weights p.d) where
  Seed := Weights p.d
  law := ⟨stdGaussian _, inferInstance⟩
  State := Scan p
  initial := start p
  query s := (0, s.cursor, s.point)
  update := advance p η
  output := output

end LongTails.Algorithms.LogisticDefectCloud
