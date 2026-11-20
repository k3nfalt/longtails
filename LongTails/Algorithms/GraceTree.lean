import LongTails.Setups.GraphBandwidthSmoothNonconvex
import Mathlib.Logic.Function.Iterate

namespace LongTails.Algorithms.GraceTree

open LongTails.Setups.GraphBandwidthSmoothNonconvex

structure Tree (p : Params) (S : Finset (Fin p.n)) (r : Fin p.n) where
  nodes : Finset (Fin p.n)
  terminals : S ⊆ nodes
  root_mem : r ∈ nodes
  parent : Fin p.n → Fin p.n
  depth : Fin p.n → ℕ
  depth_root : depth r = 0
  parent_root : parent r = r
  parent_mem : ∀ i ∈ nodes, parent i ∈ nodes
  parent_edge : ∀ i ∈ nodes, i ≠ r → p.G.Adj i (parent i)
  parent_depth : ∀ i ∈ nodes, i ≠ r → depth (parent i) + 1 = depth i

variable {p : Params} {S : Finset (Fin p.n)} {r : Fin p.n}

def Tree.atLevel (T : Tree p S r) (l : ℕ) (i : Fin p.n) :=
  T.parent^[T.depth i - l] i

def Tree.children (T : Tree p S r) (u : Fin p.n) :=
  T.nodes.filter (fun v => v ≠ r ∧ T.parent v = u)

def Tree.subtotal (T : Tree p S r) (a : Fin p.n → ℕ) (l : ℕ) (u : Fin p.n) :=
  ∑ i ∈ S, if T.atLevel l i = u then a i else 0

end LongTails.Algorithms.GraceTree
