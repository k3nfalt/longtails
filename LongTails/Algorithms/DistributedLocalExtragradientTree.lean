import LongTails.Setups.DistributedJacobianStrongGrowth
import LongTails.Algorithms.LocalExtragradientQuantization

namespace LongTails.Algorithms.DistributedLocalExtragradientTree

open LongTails.Setups.DistributedJacobianStrongGrowth

noncomputable def children (p : Params) (v : Fin p.n) : Finset (Fin p.n) :=
  Finset.univ.filter (fun u => u ≠ p.root ∧ p.parent u = v)

def ancestor (p : Params) : ℕ → Fin p.n → Fin p.n
  | 0, v => v
  | k + 1, v => ancestor p k (p.parent v)

def Descendant (p : Params) (v u : Fin p.n) : Prop :=
  ∃ k, ancestor p k u = v ∧ p.depth v + k = p.depth u

noncomputable def subtree (p : Params) (v : Fin p.n) : Finset (Fin p.n) := by
  classical
  exact Finset.univ.filter (Descendant p v)

structure Collector (n d : ℕ) where
  seen : Finset (Fin n)
  total : Fin d → ℕ

def emptyCollector {n d : ℕ} (own : Fin d → ℕ) : Collector n d :=
  ⟨∅, own⟩

noncomputable def accept {n d : ℕ} (allowed : Finset (Fin n))
    (state : Collector n d) (sender : Fin n) (payload : Fin d → ℕ) : Collector n d :=
  if sender ∈ allowed ∧ sender ∉ state.seen then
    ⟨insert sender state.seen, fun j => state.total j + payload j⟩
  else state

end LongTails.Algorithms.DistributedLocalExtragradientTree
