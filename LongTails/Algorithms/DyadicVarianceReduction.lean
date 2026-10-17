import LongTails.Algorithms.NormalizedStorm
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace OracleTemplate.DyadicHolder

open OracleTemplate.NormalizedStorm

structure DyadicConfig where
  η : ℝ
  K : ℕ
  J : ℕ
  bA : ℕ
  b : ℕ → ℕ

def DyadicConfig.pos (cfg : DyadicConfig) (k : ℕ) : ℕ := k % 2 ^ cfg.J

def DyadicConfig.level (cfg : DyadicConfig) (k : ℕ) : ℕ := padicValNat 2 (cfg.pos k)

def DyadicConfig.pred (cfg : DyadicConfig) (k : ℕ) : ℕ := k - 2 ^ cfg.level k

def DyadicConfig.batch (cfg : DyadicConfig) (k : ℕ) : ℕ :=
  if cfg.pos k = 0 then cfg.bA else cfg.b (cfg.level k)

structure DyadicState (E : Type) where
  k : ℕ
  i : ℕ
  acc : E
  xs : ℕ → E
  ds : ℕ → E
  tau : ℕ

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def dyadicQuery (cfg : DyadicConfig) (s : DyadicState E) : E × E :=
  if cfg.pos s.k = 0 then (s.xs s.k, s.xs s.k) else (s.xs s.k, s.xs (cfg.pred s.k))

noncomputable def dyadicEstimate (cfg : DyadicConfig) (ds : ℕ → E) (k : ℕ) (acc : E) : E :=
  if cfg.pos k = 0 then (1 / (cfg.bA : ℝ)) • acc
  else ds (cfg.pred k) + (1 / (cfg.b (cfg.level k) : ℝ)) • acc

noncomputable def dyadicUpdate (cfg : DyadicConfig) (s : DyadicState E) (r : E × E) :
    DyadicState E :=
  if cfg.K + 1 ≤ s.k then s
  else
    let acc := s.acc + (if cfg.pos s.k = 0 then r.1 else r.1 - r.2)
    if s.i + 1 < cfg.batch s.k then { s with i := s.i + 1, acc := acc }
    else
      let d := dyadicEstimate cfg s.ds s.k acc
      { k := s.k + 1, i := 0, acc := 0,
        xs := Function.update s.xs (s.k + 1) (stormStep cfg.η (s.xs s.k) d),
        ds := Function.update s.ds s.k d, tau := s.tau }

noncomputable def dyadicVR (cfg : DyadicConfig) (x0 : E) : Algorithm (E × E) (E × E) E where
  Seed := Fin (cfg.K + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (cfg.K + 1))).toMeasure, inferInstance⟩
  State := DyadicState E
  initial τ := { k := 0, i := 0, acc := 0, xs := fun _ => x0, ds := fun _ => 0, tau := τ.val }
  query s := (0, dyadicQuery cfg s)
  update := dyadicUpdate cfg
  output s := s.xs s.tau

end OracleTemplate.DyadicHolder
