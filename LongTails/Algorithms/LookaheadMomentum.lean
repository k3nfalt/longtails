import LongTails.Setups.StochasticThirdOrderSmoothNonconvex
import Mathlib.Probability.Distributions.Uniform

namespace OracleTemplate.LookaheadMomentum

open LongTails.Setups.StochasticThirdOrderSmoothNonconvex

structure Config where
  n0 : ℕ
  T : ℕ
  γ : ℝ
  η : ℝ

structure State (E : Type) where
  c : ℕ
  tau : ℕ
  x : E
  xp : E
  m : E
  acc : E

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def keep (cfg : Config) : ℝ := (1 - cfg.γ) * (2 - cfg.γ) / 2

noncomputable def weightNear (cfg : Config) : ℝ := cfg.γ * (2 - cfg.γ)

noncomputable def weightFar (cfg : Config) : ℝ := -(cfg.γ * (1 - cfg.γ) / 2)

noncomputable def stepTo (cfg : Config) (x m : E) : E := x - (cfg.η / ‖m‖) • m

noncomputable def leadNear (cfg : Config) (x xp : E) : E :=
  x + ((1 - cfg.γ) / cfg.γ) • (x - xp)

noncomputable def leadFar (cfg : Config) (x xp : E) : E :=
  x + ((2 - cfg.γ) / cfg.γ) • (x - xp)

noncomputable def lookaheadQuery (cfg : Config) (x0 : E) (s : State E) : E :=
  if s.c < cfg.n0 then x0
  else if (s.c - cfg.n0) / 2 < s.tau then
    (if (s.c - cfg.n0) % 2 = 0 then leadNear cfg (stepTo cfg s.x s.m) s.x
     else leadFar cfg (stepTo cfg s.x s.m) s.x)
  else s.x

noncomputable def lookaheadUpdate (cfg : Config) (s : State E) (r : E) : State E :=
  if s.c < cfg.n0 then
    (if s.c + 1 = cfg.n0 then { s with c := s.c + 1, acc := s.acc + r, m := (1 / (cfg.n0 : ℝ)) • (s.acc + r) }
     else { s with c := s.c + 1, acc := s.acc + r })
  else if (s.c - cfg.n0) / 2 < s.tau then
    (if (s.c - cfg.n0) % 2 = 0 then { s with c := s.c + 1, acc := r }
     else { s with c := s.c + 1, xp := s.x, x := stepTo cfg s.x s.m,
                   m := keep cfg • s.m + weightNear cfg • s.acc + weightFar cfg • r })
  else { s with c := s.c + 1 }

noncomputable def lookahead (p : Params) (cfg : Config) : Algorithm p.E p.E p.E where
  Seed := Fin (cfg.T + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (cfg.T + 1))).toMeasure, inferInstance⟩
  State := State p.E
  initial τ := { c := 0, tau := τ.val, x := p.x0, xp := p.x0, m := 0, acc := 0 }
  query s := (0, lookaheadQuery cfg p.x0 s)
  update := lookaheadUpdate cfg
  output s := s.x

end OracleTemplate.LookaheadMomentum
