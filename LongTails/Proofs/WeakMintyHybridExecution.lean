import LongTails.Proofs.WeakMintyHybridBounds
import LongTails.Proofs.Execution
import LongTails.Proofs.WeakMintyHybridBudget

namespace OracleTemplate.WeakMintyHybrid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def exactReply (F : E → E) (J : E → E →L[ℝ] E) :
    E ⊕ E → E × (E →L[ℝ] E) :=
  Sum.elim (fun x => (F x, 0)) (fun x => (0, J x))

noncomputable def step (L₁ L₂ ρ ε : ℝ) (F : E → E) (J : E → E →L[ℝ] E)
    (st : State E) : State E :=
  (hybrid L₁ L₂ ρ ε (0 : E)).update st
    (exactReply F J ((hybrid L₁ L₂ ρ ε (0 : E)).query st).2)

variable {L₁ L₂ ρ ε : ℝ} {F : E → E} {J : E → E →L[ℝ] E}

lemma step_done (y : E) : step L₁ L₂ ρ ε F J (.done y) = .done y := rfl

lemma iterate_done (y : E) (n : ℕ) : (step L₁ L₂ ρ ε F J)^[n] (.done y) = .done y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, step_done]

lemma picard_steps (x y : E) (n : ℕ) :
    (step L₁ L₂ ρ ε F J)^[n + 1] (.picard x y n) =
      finish (margin L₁ ρ) ε x
        ((fun u => x - ((1 - margin L₁ ρ / 4) / L₁) • F u)^[n] y)
        ((1 - margin L₁ ρ / 4) / L₁)
        (F ((fun u => x - ((1 - margin L₁ ρ / 4) / L₁) • F u)^[n] y)) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (step L₁ L₂ ρ ε F J)^[n + 1]
      (.picard x (x - ((1 - margin L₁ ρ / 4) / L₁) • F y) n) = _
    rw [ih, Function.iterate_succ_apply]

lemma block_progress {z : E} (h : Hyp F J L₁ L₂ ρ z)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hρ : 0 ≤ ρ) (hρL : ρ * L₁ < 2)
    (hε : 0 < ε) (x : E) :
    ∃ n ≤ innerCount (margin L₁ ρ) + 2,
      (∃ y, (step L₁ L₂ ρ ε F J)^[n] (.anchor x) = .done y ∧ ‖F y‖ ≤ ε) ∨
      (∃ x', (step L₁ L₂ ρ ε F J)^[n] (.anchor x) = .anchor x' ∧
        ‖x' - z‖ ^ 2 ≤ ‖x - z‖ ^ 2 - (margin L₁ ρ) ^ 4 * ε / (16384 * L₂)) := by
  let δ := margin L₁ ρ
  have hδ : 0 < δ := margin_pos hρL
  have hδ1 : δ ≤ 1 := margin_le_one hL₁.le hρ
  have hK := innerCount_pos hδ hδ1
  by_cases hg : ‖F x‖ ≤ ε
  · refine ⟨1, by omega, Or.inl ⟨x, ?_, hg⟩⟩
    simp [step, hybrid, exactReply, hg]
  by_cases hcap : ‖F x‖ ≤ δ ^ 2 * L₁ ^ 2 / (64 * L₂)
  · let s := modelStep (J x) (F x) (16 * L₂ / δ)
    let η := 1 / ((16 * L₂ / δ) * ‖s‖)
    have hs : (step L₁ L₂ ρ ε F J)^[3] (.anchor x) =
        finish δ ε x (x + s) η (F (x + s)) := by
      change step L₁ L₂ ρ ε F J (step L₁ L₂ ρ ε F J (step L₁ L₂ ρ ε F J (.anchor x))) = _
      have hc : ‖F x‖ ≤ (margin L₁ ρ) ^ 2 * L₁ ^ 2 / (64 * L₂) := hcap
      simp only [step, hybrid, exactReply, Sum.elim_inl, Sum.elim_inr, hg, hc, ↓reduceIte]
      rfl
    refine ⟨3, by change 3 ≤ innerCount δ + 2; omega, ?_⟩
    by_cases hv : ‖F (x + s)‖ ≤ ε
    · exact Or.inl ⟨x + s, hs.trans (by simp [finish, hv]), hv⟩
    · refine Or.inr ⟨x - (δ / 4 * η) • F (x + s), hs.trans (by simp [finish, hv]), ?_⟩
      exact cubic_progress h hL₁ hL₂ hρ hρL x hε (lt_of_not_ge hg) hcap (lt_of_not_ge hv)
  · let η := (1 - δ / 4) / L₁
    let T : E → E := fun y => x - η • F y
    let y := picardPoint F x η (innerCount δ)
    have hs : (step L₁ L₂ ρ ε F J)^[innerCount δ + 1] (.anchor x) =
        finish δ ε x y η (F y) := by
      rw [Function.iterate_succ_apply]
      have ha : step L₁ L₂ ρ ε F J (.anchor x) =
          .picard x (T x) (innerCount δ - 1) := by
        simp only [step, hybrid, exactReply, Sum.elim_inl, hg, ↓reduceIte]
        change (if ‖F x‖ ≤ δ ^ 2 * L₁ ^ 2 / (64 * L₂) then _ else _) = _
        rw [ite_eq_right hcap]
      rw [ha]
      have hKi : innerCount δ - 1 + 1 = innerCount δ := by omega
      nth_rw 1 [← hKi]
      rw [picard_steps]
      change finish δ ε x (T^[innerCount δ - 1] (T x)) η
        (F (T^[innerCount δ - 1] (T x))) = _
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, hKi]
      rfl
    refine ⟨innerCount δ + 1, by change innerCount δ + 1 ≤ innerCount δ + 2; omega, ?_⟩
    by_cases hv : ‖F y‖ ≤ ε
    · exact Or.inl ⟨y, hs.trans (by simp [finish, hv]), hv⟩
    · refine Or.inr ⟨x - (δ / 4 * η) • F y, hs.trans (by simp [finish, hv]), ?_⟩
      exact fallback_progress h hL₁ hL₂ hρ hρL x hε (le_of_not_ge hg) (le_of_not_ge hcap)

lemma many_blocks {z : E} (h : Hyp F J L₁ L₂ ρ z)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hρ : 0 ≤ ρ) (hρL : ρ * L₁ < 2)
    (hε : 0 < ε) (x0 : E) (N : ℕ) :
    ∃ n ≤ N * (innerCount (margin L₁ ρ) + 2),
      (∃ y, (step L₁ L₂ ρ ε F J)^[n] (.anchor x0) = .done y ∧ ‖F y‖ ≤ ε) ∨
      (∃ x, (step L₁ L₂ ρ ε F J)^[n] (.anchor x0) = .anchor x ∧
        ‖x - z‖ ^ 2 ≤ ‖x0 - z‖ ^ 2 - N * ((margin L₁ ρ) ^ 4 * ε / (16384 * L₂))) := by
  induction N with
  | zero => exact ⟨0, by simp, Or.inr ⟨x0, rfl, by simp⟩⟩
  | succ N ih =>
    obtain ⟨n, hn, hd | ⟨x, hx, hb⟩⟩ := ih
    · exact ⟨n, hn.trans (Nat.mul_le_mul_right _ (Nat.le_succ N)), Or.inl hd⟩
    · obtain ⟨m, hm, ⟨y, hy, hacc⟩ | ⟨x', hx', hb'⟩⟩ := block_progress h hL₁ hL₂ hρ hρL hε x
      · refine ⟨m + n, ?_, Or.inl ⟨y, ?_, hacc⟩⟩
        · rw [Nat.succ_mul]
          omega
        · rw [Function.iterate_add_apply, hx, hy]
      · refine ⟨m + n, ?_, Or.inr ⟨x', ?_, ?_⟩⟩
        · rw [Nat.succ_mul]
          omega
        · rw [Function.iterate_add_apply, hx, hx']
        · push_cast
          linarith

lemma done_within {z : E} (h : Hyp F J L₁ L₂ ρ z)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hρ : 0 ≤ ρ) (hρL : ρ * L₁ < 2)
    (hε : 0 < ε) (x0 : E) {N : ℕ}
    (hN : ‖x0 - z‖ ^ 2 < N * ((margin L₁ ρ) ^ 4 * ε / (16384 * L₂))) :
    ∃ n ≤ N * (innerCount (margin L₁ ρ) + 2), ∃ y,
      (step L₁ L₂ ρ ε F J)^[n] (.anchor x0) = .done y ∧ ‖F y‖ ≤ ε := by
  obtain ⟨n, hn, hd | ⟨x, _, hb⟩⟩ := many_blocks h hL₁ hL₂ hρ hρL hε x0 N
  · exact ⟨n, hn, hd⟩
  · nlinarith [sq_nonneg ‖x - z‖]

lemma done_after {x0 : E} {N K : ℕ}
    (hK : N ≤ K)
    (h : ∃ n ≤ N, ∃ y, (step L₁ L₂ ρ ε F J)^[n] (.anchor x0) = .done y ∧ ‖F y‖ ≤ ε) :
    ∃ y, (step L₁ L₂ ρ ε F J)^[K] (.anchor x0) = .done y ∧ ‖F y‖ ≤ ε := by
  obtain ⟨n, hn, y, hy, hacc⟩ := h
  refine ⟨y, ?_, hacc⟩
  rw [show K = (K - n) + n by omega, Function.iterate_add_apply, hy, iterate_done]

lemma execute_accurate {z : E} (h : Hyp F J L₁ L₂ ρ z)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hρ : 0 ≤ ρ) (hρL : ρ * L₁ < 2)
    (hε : 0 < ε) (x0 : E) {N K : ℕ}
    (hN : ‖x0 - z‖ ^ 2 < N * ((margin L₁ ρ) ^ 4 * ε / (16384 * L₂)))
    (hK : N * (innerCount (margin L₁ ρ) + 2) ≤ K)
    (oracle : Oracle (E ⊕ E) (E × (E →L[ℝ] E)))
    (hF : ∀ k seed x, oracle.answer k (0, Sum.inl x) seed = (F x, 0))
    (hJ : ∀ k seed x, oracle.answer k (0, Sum.inr x) seed = (0, J x))
    (seed : (hybrid L₁ L₂ ρ ε x0).Seed) (ξ : (k : ℕ) → oracle.Seed k) :
    ‖F (execute oracle (hybrid L₁ L₂ ρ ε x0) (fun _ => K) seed ξ)‖ ≤ ε := by
  obtain ⟨y, hy, hacc⟩ := done_after hK (done_within h hL₁ hL₂ hρ hρL hε x0 hN)
  have horacle : ∀ k query seed, oracle.answer k (0, query) seed = exactReply F J query := by
    intro k query seed
    cases query with
    | inl x => exact hF k seed x
    | inr x => exact hJ k seed x
  rw [execute_eq_of_answer_eq oracle (exactReply F J) horacle
    (hybrid L₁ L₂ ρ ε x0) K seed ξ, execute_iterate]
  change ‖F ((hybrid L₁ L₂ ρ ε x0).output ((step L₁ L₂ ρ ε F J)^[K] (.anchor x0)))‖ ≤ ε
  rw [hy]
  exact hacc

end OracleTemplate.WeakMintyHybrid
