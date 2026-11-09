import LongTails.Algorithms.CovarianceAcceleratedMixture
import LongTails.Algorithms.MultiplicativeRobustEstimator
import LongTails.Template

open Convexity
open LongTails.Algorithms.CovarianceAcceleratedMixture

namespace LongTails.Algorithms.CovarianceAccelerated

structure Config (E : Type*) (n : ℕ) where
  centers : Fin n → E
  initialIndex : Fin n
  x0 : E
  window : ℕ
  a : ℝ
  η : ℝ
  β : ℝ
  γ : ℝ

abbrev State {E : Type*} {n : ℕ} (c : Config E n) :=
  ℕ × E × StdSimplex ℝ (Fin n) × (Fin (c.window + 1) → E)

noncomputable def weight (η : ℝ) (t : ℕ) : ℝ := η * ((t : ℝ) + 1)

noncomputable def cumulative (η : ℝ) (t : ℕ) : ℝ := η * (t : ℝ) * ((t : ℝ) + 1) / 2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

noncomputable def initial (c : Config E n) : State c :=
  (0, c.x0, StdSimplex.single c.initialIndex, fun _ => 0)

noncomputable def push {k : ℕ} (v : Fin (k + 1) → E) (g : E) : Fin (k + 1) → E :=
  Fin.cases g (fun i => v i.castSucc)

noncomputable def query (c : Config E n) (s : State c) : E :=
  if s.1 < c.window + 1 then c.x0 else
    let t := s.1 - (c.window + 1)
    couple (cumulative c.η t) (weight c.η t) s.2.1 (c.x0 + c.a • mean c.centers s.2.2.1)

noncomputable def advance (c : Config E n) (s : State c) (g : E) : State c :=
  if s.1 < c.window + 1 then
    (s.1 + 1, s.2.1, s.2.2.1, push s.2.2.2 g)
  else
    let t := s.1 - (c.window + 1)
    let h := OracleTemplate.MultiplicativeRobustEstimator.medoid s.2.2.2
    let p := step c.centers c.x0 c.a (weight c.η t) c.β c.γ s.2.2.1 h g
    (s.1 + 1, couple (cumulative c.η t) (weight c.η t) s.2.1 (c.x0 + c.a • mean c.centers p),
      p, push s.2.2.2 g)

noncomputable def method (c : Config E n) : OracleTemplate.Algorithm E E E where
  State := State c
  initial := fun _ => initial c
  query := fun s => (0, query c s)
  update := advance c
  output := fun s => s.2.1

noncomputable def trajectory {Ω : Type*} (c : Config E n) (g : E → Ω → E)
    (ξ : ℕ → Ω) : ℕ → State c
  | 0 => initial c
  | t + 1 =>
      let s := trajectory c g ξ t
      advance c s (g (query c s) (ξ t))

noncomputable def output {Ω : Type*} (c : Config E n) (g : E → Ω → E)
    (ξ : ℕ → Ω) (N : ℕ) : E := (trajectory c g ξ N).2.1

end LongTails.Algorithms.CovarianceAccelerated
