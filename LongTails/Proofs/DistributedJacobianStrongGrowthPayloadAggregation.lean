import LongTails.Proofs.DistributedJacobianStrongGrowthPayload
import LongTails.Proofs.DistributedJacobianStrongGrowthTree

namespace LongTails.Proofs.DistributedJacobianStrongGrowthPayloadAggregation

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTree
open LongTails.Algorithms.DistributedLocalExtragradientMedianSearch
open LongTails.Algorithms.LocalExtragradientQuantization
open DistributedJacobianStrongGrowthTree

noncomputable def subtreeValues (p : Params) (v : Fin p.n) (values : Fin p.n → Fin p.d → ℕ) : Fin p.d → ℕ :=
  fun j => ∑ u ∈ subtree p v, values u j

def CollectorCorrect (p : Params) (v : Fin p.n) (values : Fin p.n → Fin p.d → ℕ)
    (collector : Collector p.n p.d) : Prop :=
  collector.seen ⊆ children p v ∧
    ∀ j, collector.total j = ∑ u ∈ collector.seen, subtreeValues p u values j

lemma collectorCorrect_empty (p : Params) (v : Fin p.n) (values : Fin p.n → Fin p.d → ℕ) :
    CollectorCorrect p v values (emptyCollector (fun _ => 0)) := by
  constructor
  · exact Finset.empty_subset _
  · intro j
    simp [emptyCollector]

lemma collectorCorrect_accept (p : Params) (v : Fin p.n) (values : Fin p.n → Fin p.d → ℕ)
    (collector : Collector p.n p.d) (h : CollectorCorrect p v values collector) (sender : Fin p.n) :
    CollectorCorrect p v values (accept (children p v) collector sender (subtreeValues p sender values)) := by
  have hh := accept_preserves (children p v) collector (fun _ => 0) (fun u => subtreeValues p u values)
    h.1 (by simpa using h.2) sender
  simpa [CollectorCorrect] using hh

lemma collectorCorrect_complete (p : Params) (hp : valid p) (v : Fin p.n)
    (values : Fin p.n → Fin p.d → ℕ) (collector : Collector p.n p.d)
    (h : CollectorCorrect p v values collector) (hc : children p v ⊆ collector.seen) :
    ∀ j, values v j + collector.total j = subtreeValues p v values j := by
  have he := Finset.Subset.antisymm h.1 hc
  intro j
  rw [h.2, he]
  exact (subtree_sum p hp v (fun u => values u j)).symm

lemma subtreeValues_count_fits (p : Params) (v : Fin p.n) (values : Fin p.n → Fin p.d → ℕ)
    (hv : ∀ u j, values u j ≤ 1) : ∀ j, subtreeValues p v values j < 2 ^ countWidth p.n := by
  intro j
  have hh := subtree_sum_le p v (fun u => values u j) 1 (fun u => hv u j)
  exact (by simpa [subtreeValues] using hh : subtreeValues p v values j ≤ (p.n : ℕ)).trans_lt Nat.lt_log2_self

lemma subtreeValues_grid_fits (p : Params) (v : Fin p.n) (width : ℕ)
    (values : Fin p.n → Fin p.d → ℕ) (hv : ∀ u j, values u j < 2 ^ width) :
    ∀ j, subtreeValues p v values j < 2 ^ (width + countWidth p.n) := by
  intro j
  have hh := subtree_sum_le p v (fun u => values u j) (2 ^ width) (fun u => (hv u j).le)
  have hn : (p.n : ℕ) < 2 ^ countWidth p.n := Nat.lt_log2_self
  have hm := Nat.mul_lt_mul_of_pos_right hn (by positivity : 0 < 2 ^ width)
  calc
    subtreeValues p v values j ≤ (p.n : ℕ) * 2 ^ width := hh
    _ < 2 ^ countWidth p.n * 2 ^ width := hm
    _ = 2 ^ (width + countWidth p.n) := by rw [pow_add, Nat.mul_comm]

lemma collectorCorrect_packet (p : Params) (v child : Fin p.n) (width : ℕ)
    (values : Fin p.n → Fin p.d → ℕ) (collector : Collector p.n p.d)
    (h : CollectorCorrect p v values collector)
    (hfit : ∀ j, subtreeValues p child values j < 2 ^ width) (padding : List Bool) :
    CollectorCorrect p v values (accept (children p v) collector child
      (receiveNaturals p.d width (naturalMessage width (subtreeValues p child values) ++ padding))) := by
  rw [LongTails.Proofs.LocalExtragradientQuantization.receiveNaturals_message width _ hfit padding]
  exact collectorCorrect_accept p v values collector h child

lemma collectorCorrect_update_child (p : Params) (hp : valid p) (v child : Fin p.n)
    (s : State p) (values : Fin p.n → Fin p.d → ℕ)
    (hchild : child ∈ children p v) (h : CollectorCorrect p v values s.collector)
    (hfit : ∀ j, subtreeValues p child values j < 2 ^ upWidth p s.phase) (padding : List Bool) :
    CollectorCorrect p v values (update p v s (.received ⟨child,
      naturalMessage (upWidth p s.phase) (subtreeValues p child values) ++ padding⟩)).collector := by
  have hc : child ≠ p.root ∧ p.parent child = v := (Finset.mem_filter.mp hchild).2
  have hn : ¬ (v ≠ p.root ∧ child = p.parent v) := by
    intro hh
    exact DistributedJacobianStrongGrowthConservation.no_reverse_edge p hp child v hc.1 hh.1 hc.2 hh.2.symm
  simpa [update, hn] using collectorCorrect_packet p v child (upWidth p s.phase) values s.collector h hfit padding

end LongTails.Proofs.DistributedJacobianStrongGrowthPayloadAggregation
