import LongTails.Template
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.HessianNcsc

noncomputable def nscale {E : Type*} [NormedAddCommGroup E] (lam : ℝ) (m : E) : ℝ :=
  Real.sqrt (‖m‖ ^ 2 + lam ^ 2)

noncomputable def nphi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (η lam : ℝ) (m : E) : E :=
  -(η / nscale lam m) • m

structure IgtConfig where
  α : ℝ
  η : ℝ
  lam : ℝ
  γ : ℝ
  NA : ℕ
  NB : ℕ
  NC : ℕ
  T : ℕ

structure IgtState (E F : Type) where
  c : ℕ
  tau : ℕ
  y : F
  w : E
  u : E
  acc : E
  out : E

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def lead (cfg : IgtConfig) (w u : E) : E :=
  w + ((1 - cfg.α) / cfg.α) • nphi cfg.η cfg.lam u

noncomputable def igtQuery (cfg : IgtConfig) (x0 : E) (s : IgtState E F) : E × F :=
  if s.c < cfg.NA + cfg.NB then (x0, s.y) else (lead cfg s.w s.u, s.y)

noncomputable def mzero (cfg : IgtConfig) (acc : E) : E := (1 / (cfg.NB : ℝ)) • acc

noncomputable def igtUpdate (cfg : IgtConfig) (x0 : E) (s : IgtState E F) (r : E × F) : IgtState E F :=
  if s.c < cfg.NA then { s with c := s.c + 1, y := s.y + cfg.γ • r.2 }
  else if s.c + 1 < cfg.NA + cfg.NB then { s with c := s.c + 1, acc := s.acc + r.1 }
  else if s.c + 1 = cfg.NA + cfg.NB then
    { s with c := s.c + 1, acc := s.acc + r.1, u := mzero cfg (s.acc + r.1), w := x0 + nphi cfg.η cfg.lam (mzero cfg (s.acc + r.1)) }
  else if s.c < cfg.NA + cfg.NB + cfg.NC then { s with c := s.c + 1, y := s.y + cfg.γ • r.2 }
  else if s.c < cfg.NA + cfg.NB + cfg.NC + cfg.T then
    { s with c := s.c + 1, y := s.y + cfg.γ • r.2, u := (1 - cfg.α) • s.u + cfg.α • r.1, w := s.w + nphi cfg.η cfg.lam ((1 - cfg.α) • s.u + cfg.α • r.1), out := if s.c - (cfg.NA + cfg.NB + cfg.NC) + 1 = s.tau then s.w else s.out }
  else s

noncomputable def igtSgda (cfg : IgtConfig) (x0 : E) (y0 : F) : Algorithm (E × F) (E × F) E where
  Seed := Fin (cfg.T + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (cfg.T + 1))).toMeasure, inferInstance⟩
  State := IgtState E F
  initial τ := { c := 0, tau := τ.val, y := y0, w := x0, u := 0, acc := 0, out := x0 }
  query := fun s => (0, (igtQuery cfg x0) s)
  update := igtUpdate cfg x0
  output s := s.out

end OracleTemplate.HessianNcsc
