import LongTails.Proofs.SplitBroxCounting
import LongTails.Proofs.Execution

open scoped RealInnerProductSpace

namespace OracleTemplate.SplitBrox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure ValidOracle (M : Model E) (O : Oracle (Query E) (Reply E)) : Prop where
  first : ∀ k seed x, x ∈ M.C → O.answer k (0, .inl x) seed = .inl (M.f x, M.grad x)
  linear : ∀ k seed x r g, x ∈ M.C → 0 ≤ r →
    ∃ v ∈ M.C, ‖v - x‖ ≤ r ∧
      (∀ z ∈ M.C, ‖z - x‖ ≤ r → ⟪g, v⟫ ≤ ⟪g, z⟫) ∧
      O.answer k (0, .inr (x, r, g)) seed = .inr v

lemma invariant_update (M : Model E) {O : Oracle (Query E) (Reply E)}
    (hO : ValidOracle M O) {K : ℕ} {b R : ℝ} {s : State E}
    (hs : Invariant M K b R s) (hb : 0 < b) (k : ℕ) (seed : O.Seed k) :
    Invariant M K b R (update K M.fstar s (O.answer k (0, query K b s) seed)) ∧
    (s.completed < K → rank s + 1 ≤
      rank (update K M.fstar s (O.answer k (0, query K b s) seed))) := by
  by_cases hn : K ≤ s.completed
  · simp only [update, ite_eq_left hn]
    exact ⟨hs, by omega⟩
  have hnlt : s.completed < K := by omega
  cases hp : s.phase with
  | first =>
    have hz := mix_mem M.convex hs.momentum_mem hs.primal_mem s.completed
    have he := hO.first k seed _ hz
    simp only [query, ite_eq_right hn, hp]
    rw [he]
    exact ⟨invariant_first M hs hnlt hp, fun _ => rank_update hnlt (by simp [Matches, hp])⟩
  | «local» g cut j previous =>
    obtain ⟨v, hv, hvr, hmin, he⟩ := hO.linear k seed s.momentum (radius b j) g
      hs.momentum_mem (le_of_lt (radius_pos hb j))
    simp only [query, ite_eq_right hn, hp]
    rw [he]
    exact ⟨invariant_local M hs hnlt hb g cut j previous v hp hv hvr hmin,
      fun _ => rank_update hnlt (by simp [Matches, hp])⟩

lemma execution_state (M : Model E) {O : Oracle (Query E) (Reply E)}
    (hO : ValidOracle M O) {K : ℕ} {b R : ℝ} (hb : 0 < b)
    (hR : R ^ 2 ≤ (K : ℝ) * b ^ 2) (x0 : E)
    (hx : x0 ∈ M.C) (hd : ‖x0 - M.xstar‖ ^ 2 ≤ R ^ 2)
    (ξ : (k : ℕ) → O.Seed k) :
    let s := ((fun sc : State E × ℕ =>
      (update K M.fstar sc.1 (O.answer sc.2 (0, query K b sc.1) (ξ sc.2)), sc.2 + 1))^[3 * K]
      (⟨0, 0, x0, x0, .first⟩, 0)).1
    Invariant M K b R s ∧ s.completed = K := by
  dsimp only
  let F : State E × ℕ → State E × ℕ := fun sc =>
    (update K M.fstar sc.1 (O.answer sc.2 (0, query K b sc.1) (ξ sc.2)), sc.2 + 1)
  let start : State E × ℕ := (⟨0, 0, x0, x0, .first⟩, 0)
  have hi : ∀ t, Invariant M K b R (F^[t] start).1 ∧
      ((F^[t] start).1.completed = K ∨ t ≤ rank (F^[t] start).1) := by
    intro t
    induction t with
    | zero => exact ⟨invariant_initial M K b R x0 hx hd, Or.inr (Nat.zero_le _)⟩
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      have hu := invariant_update M hO ih.1 hb (F^[t] start).2 (ξ (F^[t] start).2)
      refine ⟨hu.1, ?_⟩
      by_cases hn : (F^[t] start).1.completed = K
      · left
        change (update K M.fstar _ _).completed = K
        unfold update
        rw [ite_eq_left (show K ≤ (F^[t] start).1.completed by omega)]
        exact hn
      · right
        have hlt : (F^[t] start).1.completed < K := by have := ih.1.completed_le; omega
        have hr := hu.2 hlt
        have ht := ih.2.resolve_left hn
        exact le_trans (Nat.succ_le_succ ht) hr
  have hf := hi (3 * K)
  refine ⟨hf.1, ?_⟩
  change (F^[3 * K] start).1.completed = K
  rcases hf.2 with h | h
  · exact h
  · by_contra hn
    have hlt : (F^[3 * K] start).1.completed < K := by have := hf.1.completed_le; omega
    have hr := incomplete_rank M hf.1 hb hR hlt
    omega

lemma execute_energy (M : Model E) {O : Oracle (Query E) (Reply E)}
    (hO : ValidOracle M O) {K : ℕ} {b R : ℝ} (hb : 0 < b)
    (hR : R ^ 2 = (K : ℝ) * b ^ 2) (x0 : E)
    (hx : x0 ∈ M.C) (hd : ‖x0 - M.xstar‖ ^ 2 ≤ R ^ 2)
    (seed : (algorithm K b M.fstar x0).Seed) (ξ : (k : ℕ) → O.Seed k) :
    let y := execute O (algorithm K b M.fstar x0) (fun _ => 3 * K) seed ξ
    y ∈ M.C ∧ potentialWeight K * (M.f y - M.fstar) ≤ 5 * M.L * R ^ 2 := by
  dsimp only
  rw [execute_indexed]
  let s : State E := ((fun sc : State E × ℕ =>
      (update K M.fstar sc.1 (O.answer sc.2 (0, query K b sc.1) (ξ sc.2)), sc.2 + 1))^[3 * K]
      (⟨0, 0, x0, x0, .first⟩, 0)).1
  have hs : Invariant M K b R s ∧ s.completed = K :=
    execution_state M hO hb (le_of_eq hR) x0 hx hd ξ
  refine ⟨hs.1.primal_mem, ?_⟩
  have he := hs.1.energy
  rw [hs.2] at he
  have hn : 0 ≤ 4 * M.L * ‖s.momentum - M.xstar‖ ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) M.L_nonneg) (sq_nonneg _)
  have hmul := congrArg (fun v : ℝ => M.L * v) hR
  have hg : potentialWeight K * (M.f s.primal - M.fstar) ≤ 5 * M.L * R ^ 2 := by
    nlinarith
  simpa only [s, algorithm] using hg

end OracleTemplate.SplitBrox
