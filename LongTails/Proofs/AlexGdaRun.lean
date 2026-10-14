import LongTails.Algorithms.AlexGda
import LongTails.Proofs.AlexGdaStep
import LongTails.Proofs.Execution

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.BlockSaddle

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

section Run

variable (gx : E × F → E) (gy : E × F → F) (γ δ α β : ℝ) (x0 : E) (y0 : F)

noncomputable def iter (k : ℕ) : E × F × F := (next gx gy γ δ α β)^[k] (x0, y0, 0)

lemma iter_succ (k : ℕ) :
    iter gx gy γ δ α β x0 y0 (k + 1) = next gx gy γ δ α β (iter gx gy γ δ α β x0 y0 k) :=
  Function.iterate_succ_apply' _ _ _

noncomputable def record : ℕ → (E × F) × ℝ
  | 0 => ((x0, y0), 0)
  | k + 1 =>
    (if k = 0 ∨ progress gx gy γ δ α β (iter gx gy γ δ α β x0 y0 k) < (record k).2 then
        ((iter gx gy γ δ α β x0 y0 k).1, (iter gx gy γ δ α β x0 y0 k).2.1)
      else (record k).1,
     if k = 0 ∨ progress gx gy γ δ α β (iter gx gy γ δ α β x0 y0 k) < (record k).2 then
        progress gx gy γ δ α β (iter gx gy γ δ α β x0 y0 k)
      else (record k).2)

lemma record_succ (k : ℕ) :
    record gx gy γ δ α β x0 y0 (k + 1) =
      (if k = 0 ∨ progress gx gy γ δ α β (iter gx gy γ δ α β x0 y0 k) <
            (record gx gy γ δ α β x0 y0 k).2 then
          ((iter gx gy γ δ α β x0 y0 k).1, (iter gx gy γ δ α β x0 y0 k).2.1)
        else (record gx gy γ δ α β x0 y0 k).1,
       if k = 0 ∨ progress gx gy γ δ α β (iter gx gy γ δ α β x0 y0 k) <
            (record gx gy γ δ α β x0 y0 k).2 then
          progress gx gy γ δ α β (iter gx gy γ δ α β x0 y0 k)
        else (record gx gy γ δ α β x0 y0 k).2) := rfl

lemma record_spec (K : ℕ) (hK : 0 < K) :
    ∃ k, k < K ∧
      (record gx gy γ δ α β x0 y0 K).1 =
        ((iter gx gy γ δ α β x0 y0 k).1, (iter gx gy γ δ α β x0 y0 k).2.1) ∧
      (record gx gy γ δ α β x0 y0 K).2 = progress gx gy γ δ α β (iter gx gy γ δ α β x0 y0 k) ∧
      ∀ j, j < K → (record gx gy γ δ α β x0 y0 K).2 ≤
        progress gx gy γ δ α β (iter gx gy γ δ α β x0 y0 j) := by
  induction K with
  | zero => exact absurd hK (lt_irrefl 0)
  | succ K ih =>
    by_cases hc : K = 0 ∨ progress gx gy γ δ α β (iter gx gy γ δ α β x0 y0 K) <
        (record gx gy γ δ α β x0 y0 K).2
    · have e1 : (record gx gy γ δ α β x0 y0 (K + 1)).1 =
          ((iter gx gy γ δ α β x0 y0 K).1, (iter gx gy γ δ α β x0 y0 K).2.1) := by
        rw [record_succ]; simp only [hc, ↓reduceIte]
      have e2 : (record gx gy γ δ α β x0 y0 (K + 1)).2 =
          progress gx gy γ δ α β (iter gx gy γ δ α β x0 y0 K) := by
        rw [record_succ]; simp only [hc, ↓reduceIte]
      refine ⟨K, Nat.lt_succ_self K, e1, e2, ?_⟩
      intro j hj
      rw [e2]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · rcases hc with h0 | hlt2
        · exact absurd (h0 ▸ hlt) (Nat.not_lt_zero j)
        · obtain ⟨_, _, _, _, hmin⟩ := ih (lt_of_le_of_lt (Nat.zero_le j) hlt)
          exact le_of_lt (lt_of_lt_of_le hlt2 (hmin j hlt))
      · rw [heq]
    · have hK0 : K ≠ 0 := fun h => hc (Or.inl h)
      have hnl : ¬ progress gx gy γ δ α β (iter gx gy γ δ α β x0 y0 K) <
          (record gx gy γ δ α β x0 y0 K).2 := fun h => hc (Or.inr h)
      have e1 : (record gx gy γ δ α β x0 y0 (K + 1)).1 = (record gx gy γ δ α β x0 y0 K).1 := by
        rw [record_succ]; simp only [hc, ↓reduceIte]
      have e2 : (record gx gy γ δ α β x0 y0 (K + 1)).2 = (record gx gy γ δ α β x0 y0 K).2 := by
        rw [record_succ]; simp only [hc, ↓reduceIte]
      obtain ⟨k, hk, h1, h2, hmin⟩ := ih (Nat.pos_of_ne_zero hK0)
      refine ⟨k, Nat.lt_succ_of_lt hk, by rw [e1, h1], by rw [e2, h2], ?_⟩
      intro j hj
      rw [e2]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · exact hmin j hlt
      · rw [heq]; exact not_lt.mp hnl

def answerFn : (E × F) ⊕ (E × F) → E ⊕ F :=
  Sum.elim (fun z => Sum.inl (gx z)) (fun z => Sum.inr (gy z))

noncomputable def stateAt (K : ℕ) : AlexState E F :=
  ⟨false, K, (iter gx gy γ δ α β x0 y0 K).1, (iter gx gy γ δ α β x0 y0 K).2.1,
    (iter gx gy γ δ α β x0 y0 K).2.2, 0, (record gx gy γ δ α β x0 y0 K).1,
    (record gx gy γ δ α β x0 y0 K).2⟩

lemma two_steps (K : ℕ) :
    (alexGda γ δ α β x0 y0).update
      ((alexGda γ δ α β x0 y0).update (stateAt gx gy γ δ α β x0 y0 K)
        (answerFn gx gy (((alexGda γ δ α β x0 y0).query (stateAt gx gy γ δ α β x0 y0 K)).2)))
      (answerFn gx gy (((alexGda γ δ α β x0 y0).query
        ((alexGda γ δ α β x0 y0).update (stateAt gx gy γ δ α β x0 y0 K)
          (answerFn gx gy
            (((alexGda γ δ α β x0 y0).query (stateAt gx gy γ δ α β x0 y0 K)).2)))).2)) =
      stateAt gx gy γ δ α β x0 y0 (K + 1) := by
  unfold stateAt
  rw [iter_succ, record_succ]
  rfl

lemma run_state (K : ℕ) :
    (fun st => (alexGda γ δ α β x0 y0).update st
      (answerFn gx gy (((alexGda γ δ α β x0 y0).query st).2)))^[2 * K]
      ((alexGda γ δ α β x0 y0).initial ()) = stateAt gx gy γ δ α β x0 y0 K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 + 2 * K by ring, Function.iterate_add_apply, ih]
    exact two_steps gx gy γ δ α β x0 y0 K

lemma execute_alex (K : ℕ) :
    execute { answer := fun _ (_, query) _ => answerFn gx gy query } (alexGda γ δ α β x0 y0) (fun _ => (2 * K)) =
      (record gx gy γ δ α β x0 y0 K).1 := by
  erw [execute_iterate (answerFn gx gy) (alexGda γ δ α β x0 y0) (2 * K) (), run_state]
  rfl

lemma sum_prev (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), ‖(iter gx gy γ δ α β x0 y0 k).2.2‖ ^ 2 =
      ∑ k ∈ Finset.range K, ‖gradY gx gy γ δ α β (iter gx gy γ δ α β x0 y0 k)‖ ^ 2 := by
  have h0 : (iter gx gy γ δ α β x0 y0 0).2.2 = 0 := rfl
  have hk : ∀ k, (iter gx gy γ δ α β x0 y0 (k + 1)).2.2 =
      gradY gx gy γ δ α β (iter gx gy γ δ α β x0 y0 k) := fun k => by
    rw [iter_succ]; rfl
  rw [Finset.sum_range_succ', h0, norm_zero]
  simp only [hk]
  norm_num

end Run

section Bound

variable {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F} {Lx Ly Lxy : ℝ} {xs : E} {ys : F}
  {γ δ α β : ℝ} {x0 : E} {y0 : F}

lemma sum_decrease (H : Hyp f gx gy Lx Ly Lxy xs ys)
    (hγ : 1 < γ) (hγ2 : γ ≤ 2) (hδ : 1 ≤ δ) (hα : 0 < α) (hβ : 0 < β)
    (hLy : 0 ≤ Ly) (hLxy : 0 ≤ Lxy)
    (c1 : Lx * γ ^ 2 * α ≤ (γ - 1) / 4) (c2 : γ * δ ^ 2 * Ly * β ≤ (γ - 1) / 4)
    (c3 : γ ^ 2 * δ ^ 2 * Lxy ^ 2 * (α * β) ≤ 1 / 16) (K : ℕ) :
    (γ - 1) / 4 *
        (α * ∑ k ∈ Finset.range K, ‖gradX gx δ β (iter gx gy γ δ α β x0 y0 k)‖ ^ 2 +
          β * ∑ k ∈ Finset.range K, ‖gradY gx gy γ δ α β (iter gx gy γ δ α β x0 y0 k)‖ ^ 2) ≤
      energy f gx γ δ α β xs ys (x0, y0, 0) -
        energy f gx γ δ α β xs ys (iter gx gy γ δ α β x0 y0 K) := by
  induction K with
  | zero =>
    have e : iter gx gy γ δ α β x0 y0 0 = (x0, y0, 0) := rfl
    rw [e]
    simp
  | succ K ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, iter_succ]
    have h := step_decrease H hγ hγ2 hδ hα hβ hLy hLxy c1 c2 c3 (iter gx gy γ δ α β x0 y0 K)
    linarith only [ih, h]

theorem best_bound (H : Hyp f gx gy Lx Ly Lxy xs ys)
    (hγ : 1 < γ) (hγ2 : γ ≤ 2) (hδ : 1 ≤ δ) (hα : 0 < α) (hβ : 0 < β)
    (hLx : 0 ≤ Lx) (hLy : 0 ≤ Ly) (hLxy : 0 ≤ Lxy)
    (c1 : Lx * γ ^ 2 * α ≤ (γ - 1) / 4) (c2 : γ * δ ^ 2 * Ly * β ≤ (γ - 1) / 4)
    (c3 : γ ^ 2 * δ ^ 2 * Lxy ^ 2 * (α * β) ≤ 1 / 16)
    (e1 : (Lx + Lxy) * α ≤ 1 / 16) (e2 : (Ly + Lxy) * β ≤ 1 / 16)
    (e3 : Lxy * ((δ - 1) * β) ^ 2 ≤ ((2 - γ) * (δ - 1) / 2 + 3 * (γ - 1) / 8) * β)
    (r1 : Lxy * ((δ - 1) * β) ≤ 1 / 16) (r2 : Lxy * (γ * α) ≤ 1 / 8)
    {m0 : ℝ} (hm0 : 0 < m0) (hmα : m0 ≤ α) (hmβ : m0 ≤ β) (K : ℕ) (hK : 0 < K) :
    (γ - 1) * m0 ^ 2 * K *
        (‖gx (record gx gy γ δ α β x0 y0 K).1‖ ^ 2 + ‖gy (record gx gy γ δ α β x0 y0 K).1‖ ^ 2) ≤
      45 / 4 * (‖x0 - xs‖ ^ 2 + ‖y0 - ys‖ ^ 2) := by
  obtain ⟨k, -, hz, hv, hmin⟩ := record_spec gx gy γ δ α β x0 y0 K hK
  have f1 : ‖gx (record gx gy γ δ α β x0 y0 K).1‖ ^ 2 +
      ‖gy (record gx gy γ δ α β x0 y0 K).1‖ ^ 2 ≤
      5 / 4 * (record gx gy γ δ α β x0 y0 K).2 := by
    rw [hz, hv]
    exact residual_le H hγ hδ hα hβ r1 r2 (iter gx gy γ δ α β x0 y0 k)
  have f2 : (K : ℝ) * (record gx gy γ δ α β x0 y0 K).2 ≤
      ∑ j ∈ Finset.range K, ‖gradX gx δ β (iter gx gy γ δ α β x0 y0 j)‖ ^ 2 +
        ∑ j ∈ Finset.range K, ‖gradY gx gy γ δ α β (iter gx gy γ δ α β x0 y0 j)‖ ^ 2 +
        ∑ j ∈ Finset.range K, ‖(iter gx gy γ δ α β x0 y0 j).2.2‖ ^ 2 := by
    have t : ∑ _j ∈ Finset.range K, (record gx gy γ δ α β x0 y0 K).2 ≤
        ∑ j ∈ Finset.range K, progress gx gy γ δ α β (iter gx gy γ δ α β x0 y0 j) :=
      Finset.sum_le_sum (fun j hj => hmin j (Finset.mem_range.mp hj))
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at t
    simp only [progress, Finset.sum_add_distrib] at t
    exact t
  have f3 : ∑ j ∈ Finset.range K, ‖(iter gx gy γ δ α β x0 y0 j).2.2‖ ^ 2 ≤
      ∑ j ∈ Finset.range K, ‖gradY gx gy γ δ α β (iter gx gy γ δ α β x0 y0 j)‖ ^ 2 := by
    rw [← sum_prev gx gy γ δ α β x0 y0 K, Finset.sum_range_succ]
    have := sq_nonneg ‖(iter gx gy γ δ α β x0 y0 K).2.2‖
    linarith only [this]
  have hSG : 0 ≤ ∑ j ∈ Finset.range K, ‖gradX gx δ β (iter gx gy γ δ α β x0 y0 j)‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSH : 0 ≤ ∑ j ∈ Finset.range K, ‖gradY gx gy γ δ α β (iter gx gy γ δ α β x0 y0 j)‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have f4a := mul_le_mul_of_nonneg_right hmα hSG
  have f4b := mul_le_mul_of_nonneg_right hmβ hSH
  have f5 := sum_decrease (x0 := x0) (y0 := y0) H hγ hγ2 hδ hα hβ hLy hLxy c1 c2 c3 K
  have f5' := energy_lower H hγ hγ2 hδ hα hβ hLxy e1
    (by linarith only [e2, mul_nonneg hLy hβ.le] : Lxy * β ≤ 1 / 16) e3 (iter gx gy γ δ α β x0 y0 K)
  have f5'' : 0 ≤ (‖(iter gx gy γ δ α β x0 y0 K).1 - xs‖ ^ 2 / α +
      ‖(iter gx gy γ δ α β x0 y0 K).2.1 - ys‖ ^ 2 / β) / 2 := by positivity
  have f6 := energy_init (δ := δ) H hγ hγ2 hα hβ hLx hLxy e1 e2 x0 y0
  have t1 : ‖x0 - xs‖ ^ 2 / α * m0 ≤ ‖x0 - xs‖ ^ 2 / α * α :=
    mul_le_mul_of_nonneg_left hmα (by positivity)
  have t2 : ‖y0 - ys‖ ^ 2 / β * m0 ≤ ‖y0 - ys‖ ^ 2 / β * β :=
    mul_le_mul_of_nonneg_left hmβ (by positivity)
  rw [div_mul_cancel₀ _ hα.ne'] at t1
  rw [div_mul_cancel₀ _ hβ.ne'] at t2
  have hc : 0 ≤ γ - 1 := by linarith
  have hKr : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have g1 := mul_le_mul_of_nonneg_left f1 (mul_nonneg (mul_nonneg hc (sq_nonneg m0)) hKr)
  have g2 := mul_le_mul_of_nonneg_left (show (K : ℝ) * (record gx gy γ δ α β x0 y0 K).2 ≤
      ∑ j ∈ Finset.range K, ‖gradX gx δ β (iter gx gy γ δ α β x0 y0 j)‖ ^ 2 +
        2 * ∑ j ∈ Finset.range K, ‖gradY gx gy γ δ α β (iter gx gy γ δ α β x0 y0 j)‖ ^ 2 by
      linarith only [f2, f3]) (mul_nonneg hc (sq_nonneg m0))
  have g3 : 0 ≤ (γ - 1) * m0 ^ 2 *
      ∑ j ∈ Finset.range K, ‖gradX gx δ β (iter gx gy γ δ α β x0 y0 j)‖ ^ 2 :=
    mul_nonneg (mul_nonneg hc (sq_nonneg m0)) hSG
  have g4 := mul_le_mul_of_nonneg_left (add_le_add f4a f4b) (mul_nonneg hc hm0.le)
  have g5 := mul_le_mul_of_nonneg_left f5 hm0.le
  have g5' := mul_le_mul_of_nonneg_left (le_trans f5'' f5') hm0.le
  have g6 := mul_le_mul_of_nonneg_left f6 hm0.le
  linarith only [g1, g2, g3, g4, g5, g5', g6, t1, t2]

end Bound

end OracleTemplate.BlockSaddle
