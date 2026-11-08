import LongTails.Proofs.BirchCausalControllers
import LongTails.Proofs.BirchCausalStates

namespace LongTails.Proofs.BirchCausalPlans

open Finset
open LongTails.Algorithms.BirchCausalPackets
open LongTails.Proofs.BirchCausalMerges
open LongTails.Proofs.BirchCausalControllers
open LongTails.Proofs.BirchCausalStates

lemma prefix_fresh_meet (source current work : ℕ) (hs : source ≤ current) :
    range current ∩ (range source ∪ Ico current (current + work)) = range source := by
  ext i
  simp only [mem_inter, mem_union, mem_range, mem_Ico]
  omega

lemma prefix_fresh_union (source current work : ℕ) (hs : source ≤ current) :
    range current ∪ (range source ∪ Ico current (current + work)) = range (current + work) := by
  ext i
  simp only [mem_union, mem_range, mem_Ico]
  omega

lemma packet_age (H R current source i : ℕ) (hs : source ≤ current)
    (hage : current - source ≤ R) (hi : i < current * H + H) :
    i - H * (R + 1) ≤ source * H := by
  have hc : current ≤ source + R := by omega
  have hm := Nat.mul_le_mul_right H hc
  rw [add_mul] at hm
  have he : H * (R + 1) = R * H + H := by ring
  rw [he]
  omega

structure PlanInvariant (workers H R K : ℕ) (plan : GraphPlan) : Prop where
  valid : GraphValidFrom workers {} plan.nodes
  next : (graphHistory plan.nodes).next = plan.next
  atoms : (graphHistory plan.nodes).atoms = K * H
  main_zero : plan.main 0 = 0
  main_lt : ∀ j, j ≤ K → plan.main j < plan.next
  main_history : ∀ j, j ≤ K →
    (graphHistory plan.nodes).states (plan.main j) = range (j * H)
  query_age : ∀ i, i < K * H → range (i - H * (R + 1)) ⊆ (graphHistory plan.nodes).queryHistory i

lemma planInvariant_initial (workers H R : ℕ) : PlanInvariant workers H R 0 {} := by
  constructor
  · trivial
  · rfl
  · simp [graphHistory]
  · rfl
  · intro j hj; exact Nat.zero_lt_one
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simp [graphHistory]
  · intro i hi; simp at hi

lemma planInvariant_step (workers H R K : ℕ) (packet : ℕ → PacketExpr) (source : ℕ → ℕ)
    (plan : GraphPlan) (h : PlanInvariant workers H R K plan)
    (hw : 0 < workers) (hp : (packet K).Valid workers) (hc : (packet K).calls = H)
    (hs : source K ≤ K) (hage : K - source K ≤ R) :
    PlanInvariant workers H R (K + 1) (planStep packet source K plan) := by
  let history := graphHistory plan.nodes
  let root := plan.main (source K)
  let block := (packet K).compile root plan.next
  let after := block.nodes.foldl (flip historyStep) history
  let node := GraphNode.merge 0 (plan.main K) block.output root
  let final := historyStep node after
  have hhnext : history.next = plan.next := h.next
  have hr : root < history.next := by rw [h.next]; exact h.main_lt _ hs
  have hb : BlockMeaning workers history root block H := by
    simpa only [hhnext, hc] using compile_meaning workers (packet K) hp history root hr
  have hbnext : plan.next ≤ block.next := by simpa only [hhnext] using hb.next_le
  have hn : after.next = block.next := hb.next
  have ha : after.atoms = K * H + H := by rw [hb.atoms, h.atoms]
  have hroot : after.states root = range (source K * H) := by
    rw [historyFold_old block.nodes history root hr]
    exact h.main_history _ hs
  have hhead : after.states (plan.main K) = range (K * H) := by
    rw [historyFold_old block.nodes history _ (by rw [h.next]; exact h.main_lt K le_rfl)]
    exact h.main_history K le_rfl
  have hout : after.states block.output = range (source K * H) ∪ Ico (K * H) (K * H + H) := by
    rw [hb.output, h.atoms, h.main_history _ hs]
  have hmeet : after.states root = after.states (plan.main K) ∩ after.states block.output := by
    rw [hroot, hhead, hout, prefix_fresh_meet _ _ _ (Nat.mul_le_mul_right H hs)]
  have hnode : node.Valid workers after := by
    refine ⟨hw, ?_, ?_, ?_, hmeet⟩
    · rw [hn]; exact (h.main_lt K le_rfl).trans_le hbnext
    · rw [hn]; exact hb.output_lt
    · rw [hn]; exact (h.main_lt _ hs).trans_le hbnext
  have hf : graphHistory (planStep packet source K plan).nodes = final := by
    simp only [graphHistory, planStep, List.foldl_append, List.foldl_cons, List.foldl_nil, flip]
    rfl
  have hfnext : final.next = block.next + 1 := by rw [historyStep_next, hn]
  have hfatoms : final.atoms = (K + 1) * H := by
    change after.atoms = _
    rw [ha]
    ring
  have hnew : final.states block.next = range ((K + 1) * H) := by
    change Function.update after.states after.next (after.states (plan.main K) ∪ after.states block.output) block.next = _
    rw [hn, Function.update_self, hhead, hout, prefix_fresh_union _ _ _ (Nat.mul_le_mul_right H hs)]
    congr 1
    ring
  have hold (j : ℕ) (hj : j ≤ K) : final.states (plan.main j) = range (j * H) := by
    have hjb : plan.main j < after.next := by
      rw [hn]
      exact (h.main_lt j hj).trans_le hbnext
    rw [historyStep_old node after (plan.main j) hjb]
    rw [historyFold_old block.nodes history _ (by rw [h.next]; exact h.main_lt j hj)]
    exact h.main_history j hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change GraphValidFrom workers {} (plan.nodes ++ block.nodes ++ [node])
    rw [graphValid_append, graphValid_append]
    exact ⟨⟨h.valid, hb.valid⟩, by simpa only [List.foldl_append, after, history, graphHistory] using hnode, trivial⟩
  · rw [hf]
    exact hfnext
  · rw [hf]
    exact hfatoms
  · change Function.update plan.main (K + 1) block.next 0 = 0
    rw [Function.update_of_ne (by omega)]
    exact h.main_zero
  · intro j hj
    change Function.update plan.main (K + 1) block.next j < block.next + 1
    by_cases he : j = K + 1
    · subst j; rw [Function.update_self]; omega
    · rw [Function.update_of_ne he]
      exact (h.main_lt j (by omega)).trans_le
        (hbnext.trans (Nat.le_succ _))
  · intro j hj
    rw [hf]
    change final.states (Function.update plan.main (K + 1) block.next j) = _
    by_cases he : j = K + 1
    · subst j; rw [Function.update_self]; exact hnew
    · rw [Function.update_of_ne he]; exact hold j (by omega)
  · intro i hi
    rw [hf]
    change range (i - H * (R + 1)) ⊆ after.queryHistory i
    by_cases hiold : i < K * H
    · rw [historyFold_old_queries block.nodes history i (by rw [h.atoms]; exact hiold)]
      exact h.query_age i hiold
    · have hrooted : RootedQueries (history.states root) history block.nodes := by
        simpa only [hhnext] using compile_rooted workers (packet K) hp history root hr
      have hir : history.atoms ≤ i := by rw [h.atoms]; omega
      have hin : i < after.atoms := by rw [ha]; nlinarith
      have hinc := hrooted i hir hin
      rw [h.main_history _ hs] at hinc
      exact (range_mono (packet_age H R K (source K) i hs hage (by nlinarith))).trans hinc

lemma planRun_invariant (workers H R K : ℕ) (packet : ℕ → PacketExpr) (source : ℕ → ℕ)
    (hw : 0 < workers) (hp : ∀ k, (packet k).Valid workers) (hc : ∀ k, (packet k).calls = H)
    (hs : ∀ k, source k ≤ k) (hage : ∀ k, k - source k ≤ R) :
    PlanInvariant workers H R K (planRun packet source K) := by
  induction K with
  | zero => exact planInvariant_initial workers H R
  | succ K ih => exact planInvariant_step workers H R K packet source _ ih hw (hp K) (hc K) (hs K) (hage K)

lemma plan_complete_recent (workers H R K : ℕ) (plan : GraphPlan)
    (h : PlanInvariant workers H R K plan) :
    ∀ n, range (n - H * (R + 1)) ⊆ completeHistory (graphHistory plan.nodes) n := by
  intro n
  by_cases hn : n < (graphHistory plan.nodes).atoms
  · rw [completeHistory, ite_eq_left hn]
    apply h.query_age
    rwa [h.atoms] at hn
  · rw [completeHistory, ite_eq_right hn]
    exact range_mono (Nat.sub_le _ _)

end LongTails.Proofs.BirchCausalPlans
