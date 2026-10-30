import LongTails.Algorithms.CovarianceSoftCut

noncomputable section

namespace LongTails.Algorithms.CovarianceSoftCutMethod

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Algorithms.CovarianceSoftCut

structure Config where
  α : ℝ
  a : ℝ
  b : ℕ
  H : ℕ
  K : ℕ
  n : ℕ
  m : ℕ

def generatorCost (c : Config) : ℕ := 2^c.H*c.b

def selectionCost (c : Config) : ℕ := selectionBlocks c.K c.H*(c.n*c.m)

def workCost (c : Config) : ℕ := generatorCost c + selectionCost c

def leaves (q : Params) (c : Config) (replies : ℕ → Space q) (i : ℕ) : Space q :=
  if i < 2^c.H then generatorPoint q c.α (2/c.α) c.b i replies else 0

def suffix (q : Params) (c : Config) (replies : ℕ → Space q) (i : ℕ) : Space q :=
  replies (generatorCost c+i)

def query (q : Params) (c : Config) (t : ℕ) (replies : ℕ → Space q) : Space q :=
  if t < generatorCost c then generatorPoint q c.α (2/c.α) c.b (t/c.b) replies
  else if t < workCost c then
    (selectionProbe q c.a c.K c.n c.m c.H (leaves q c replies) (suffix q c replies)
      ((t-generatorCost c)/(c.n*c.m))).1
  else 0

def output (q : Params) (c : Config) (replies : ℕ → Space q) : Space q :=
  selectionOutput q c.a c.K c.n c.m c.H (leaves q c replies) (suffix q c replies)

def method (q : Params) (c : Config) : OracleTemplate.Algorithm (Space q) (Space q) (Space q) :=
  historyMethod q (query q c) (output q c)

def tunedConfig (q : Params) : Config :=
  let H := ⌈Real.log (24*(1+(q.d : ℝ)*Real.log (16*q.L*q.R/q.ε)))/Real.log 2⌉₊
  let τ := q.ε/(2*(H : ℝ))
  let a := τ/(12*q.R)
  let K := ⌈Real.log (4*q.L*q.R/τ)/Real.log 2⌉₊
  { α := q.ε/2
    a := a
    b := max 1 ⌈4096*q.σ^2*q.R^2/((q.d : ℝ)*q.ε^2)⌉₊
    H := H
    K := K
    n := max 1 ⌈8*q.σ^2/((q.d : ℝ)*a^2)⌉₊
    m := 2*⌈4*Real.log (12*(max 1 (selectionBlocks K H) : ℕ))⌉₊+1 }

def tunedMethod (q : Params) : OracleTemplate.Algorithm (Space q) (Space q) (Space q) :=
  if q.ε < q.L*q.R then method q (tunedConfig q)
  else historyMethod q (fun _ _ => 0) (fun _ => 0)

end LongTails.Algorithms.CovarianceSoftCutMethod
