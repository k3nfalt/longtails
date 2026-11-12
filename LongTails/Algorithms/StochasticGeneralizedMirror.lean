import LongTails.Setups.StochasticGeneralizedMirror
import LongTails.Algorithms.RobustGradientEstimator

namespace LongTails.Algorithms.StochasticGeneralizedMirror

noncomputable def mix {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A a : ℝ) (x z : E) : E := (A / (A + a)) • x + (a / (A + a)) • z

open LongTails.Setups.StochasticGeneralizedMirror

noncomputable def clipRadius (q : Public) : ℝ :=
  96 * q.σ + q.ε / q.R + 2 * (256 * q.σ ^ q.α * q.R / q.ε) ^ (1 / (q.α - 1))

noncomputable def noiseMoment (q : Public) : ℝ :=
  4 * clipRadius q ^ (2 - q.α) * q.σ ^ q.α

noncomputable def initialWeight (q : Public) : ℝ := q.R ^ 2 / (8 * (q.Δ + q.ε))

noncomputable def stepWeight (q : Public) (ell A : ℝ) : ℝ :=
  min (A / (1024 * (1 + q.L1 * q.R)))
    (min (Real.sqrt A / (128 * Real.sqrt (q.L0 + q.L1 * q.G)))
      (min (q.R / (65536 * clipRadius q * ell))
        (q.ε / (65536 * (noiseMoment q + q.ε ^ 2 / q.R ^ 2) * ell))))

structure State (q : Public) (m : ℕ) where
  A : ℝ
  x : q.E
  z : q.E
  stage : ℕ
  received : ℕ
  pilot : Fin m → Dual q
  center : Dual q
  direction : Dual q

noncomputable def initialState (q : Public) (m : ℕ) : State q m where
  A := initialWeight q
  x := q.x0
  z := q.x0
  stage := 0
  received := 0
  pilot := fun _ => 0
  center := 0
  direction := 0

noncomputable def query (q : Public) (ell : ℝ) {m : ℕ} (s : State q m) : Query q :=
  if q.R ^ 2 / q.ε ≤ s.A then .gradient q.x0
  else if s.stage = 2 then .prox (stepWeight q ell s.A) s.z s.direction
  else .gradient (mix s.A (stepWeight q ell s.A) s.x s.z)

noncomputable def storePilot {q : Public} {m : ℕ} (s : State q m) (v : Dual q) :
    Fin m → Dual q := fun i => if i.val = s.received then v else s.pilot i

noncomputable def update (q : Public) (ell : ℝ) {m : ℕ} (s : State q m)
    (reply : Reply q) : State q m := by
  classical
  exact if q.R ^ 2 / q.ε ≤ s.A then s else
    match reply with
    | Sum.inl v =>
        if s.stage = 0 then
          let pilot := storePilot s v
          if s.received + 1 = m then
            { s with
              stage := 1
              pilot := pilot
              center := OracleTemplate.RobustGradient.pilotCenter (clipRadius q) pilot }
          else { s with received := s.received + 1, pilot := pilot }
        else if s.stage = 1 then
          { s with
            stage := 2
            direction := OracleTemplate.RobustGradient.centeredClip (clipRadius q) s.center v }
        else s
    | Sum.inr p =>
        if s.stage = 2 then
          { s with
            A := s.A + stepWeight q ell s.A
            x := mix s.A (stepWeight q ell s.A) s.x p
            z := p
            stage := 0
            received := 0
            pilot := fun _ => 0
            center := 0
            direction := 0 }
        else s

def lastIterate {q : Public} {m : ℕ} (s : State q m) : q.E := s.x

noncomputable def algorithm (q : Public) (ell : ℝ) (m : ℕ) :
    OracleTemplate.Algorithm (Query q) (Reply q) q.E where
  State := State q m
  initial _ := initialState q m
  query s := (0, query q ell s)
  update := update q ell
  output := lastIterate

end LongTails.Algorithms.StochasticGeneralizedMirror
