import LongTails.Setups.StochasticCompositeHessianLipschitz
import Mathlib.Probability.Distributions.Uniform

namespace OracleTemplate.CompositeTransport

open LongTails.Setups.StochasticCompositeHessianLipschitz

structure Config where
  n0 : ℕ
  T : ℕ
  α : ℝ
  γ : ℝ
  ε : ℝ

structure State (E : Type) where
  c : ℕ
  tau : ℕ
  x : E
  xp : E
  m : E
  acc : E

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def capStep (cfg : Config) (x r : E) : E :=
  x + min 1 (2 * cfg.γ * cfg.ε / ‖r - x‖) • (r - x)

noncomputable def lead (cfg : Config) (x xp : E) : E :=
  x + ((1 - cfg.α) / cfg.α) • (x - xp)

noncomputable def transportQuery (p : Params) (cfg : Config) (s : State p.E) : Query p :=
  if s.c < cfg.n0 then .gradient p.x0
  else if (s.c - cfg.n0) / 2 < s.tau then
    (if (s.c - cfg.n0) % 2 = 0 then .prox cfg.γ s.x s.m else .gradient (lead cfg s.x s.xp))
  else .gradient s.x

noncomputable def transportUpdate (cfg : Config) (s : State E) (r : E) : State E :=
  if s.c < cfg.n0 then
    (if s.c + 1 = cfg.n0 then { s with c := s.c + 1, acc := s.acc + r, m := (1 / (cfg.n0 : ℝ)) • (s.acc + r) }
     else { s with c := s.c + 1, acc := s.acc + r })
  else if (s.c - cfg.n0) / 2 < s.tau then
    (if (s.c - cfg.n0) % 2 = 0 then { s with c := s.c + 1, xp := s.x, x := capStep cfg s.x r }
     else { s with c := s.c + 1, m := (1 - cfg.α) • s.m + cfg.α • r })
  else { s with c := s.c + 1 }

noncomputable def transport (p : Params) (cfg : Config) : Algorithm (Query p) p.E p.E where
  Seed := Fin (cfg.T + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (cfg.T + 1))).toMeasure, inferInstance⟩
  State := State p.E
  initial τ := { c := 0, tau := τ.val, x := p.x0, xp := p.x0, m := 0, acc := 0 }
  query s := (0, transportQuery p cfg s)
  update := transportUpdate cfg
  output s := s.x

end OracleTemplate.CompositeTransport
