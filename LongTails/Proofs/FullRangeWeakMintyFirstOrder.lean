import LongTails.Algorithms.FullRangeWeakMintyFirstOrder
import LongTails.Proofs.WeakMintyHybridExecution

open scoped RealInnerProductSpace

namespace OracleTemplate.FullRangeWeakMintyFirstOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def potential (b : ℝ) (u g h : E) : ℝ :=
  ‖u + (1 - b) • h‖ ^ 2 + ‖g - h‖ ^ 2 - 2 * (1 - b) * b * ‖h‖ ^ 2

private lemma potential_nonneg {b : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1 / 4)
    {u g : E} (h : E) (hr : ‖g‖ ≤ ‖u‖)
    (hm : -(1 - 4 * b) * ‖g‖ ^ 2 ≤ ⟪g, u⟫) : 0 ≤ potential b u g h := by
  let a := 1 - b
  let C := 1 + a ^ 2 - 2 * a * b
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hc : 0 < 1 - 2 * a * b := by dsimp [a]; nlinarith [sq_nonneg b]
  have hC : 0 < C := by dsimp [C]; nlinarith [sq_nonneg a]
  have hid : C * potential b u g h = ‖C • h + a • u - g‖ ^ 2 +
      (1 - 2 * a * b) * (‖u‖ ^ 2 - ‖g‖ ^ 2) + 2 * a * (⟪g, u⟫ + (1 - 4 * b) * ‖g‖ ^ 2) +
      (b ^ 2 + 4 * a * b) * ‖g‖ ^ 2 := by
    simp only [potential, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, real_inner_smul_right,
      real_inner_comm, C, a]
    ring
  have hu := pow_le_pow_left₀ (norm_nonneg _) hr 2
  have hm' : 0 ≤ ⟪g, u⟫ + (1 - 4 * b) * ‖g‖ ^ 2 := by linarith
  apply nonneg_of_mul_nonneg_right (a := C) _ hC
  rw [hid]
  exact add_nonneg (add_nonneg (add_nonneg (sq_nonneg _)
    (mul_nonneg hc.le (sub_nonneg.mpr hu))) (mul_nonneg (by positivity) hm'))
    (by positivity)

private lemma potential_step {b : ℝ} (hb : 0 ≤ b) (u g h v : E)
    (hm : -(1 - 4 * b) * ‖g‖ ^ 2 ≤ ⟪g, u⟫)
    (hl : ‖v - g‖ ≤ ‖(1 - b) • h - g‖) :
    potential b (u - g + (1 - b) • h) v g - potential b u g h ≤
      -(4 * b) ^ 2 / 4 * ‖g‖ ^ 2 - b ^ 2 * ‖g - h‖ ^ 2 := by
  have hid : potential b (u - g + (1 - b) • h) v g - potential b u g h +
      (4 * b) ^ 2 / 4 * ‖g‖ ^ 2 + b ^ 2 * ‖g - h‖ ^ 2 =
      (‖v - g‖ ^ 2 - ‖(1 - b) • h - g‖ ^ 2) - 2 * b * (⟪g, u⟫ + (1 - 4 * b) * ‖g‖ ^ 2) := by
    simp only [potential, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, real_inner_smul_right,
      real_inner_comm]
    ring
  have hs := pow_le_pow_left₀ (norm_nonneg _) hl 2
  have hm' : 0 ≤ 2 * b * (⟪g, u⟫ + (1 - 4 * b) * ‖g‖ ^ 2) := mul_nonneg (by positivity) (by linarith)
  linarith

open WeakMintyHybrid (margin)

lemma value_execute_accurate {F : E → E} {z : E} {L ρ ε R : ℝ}
    (hL : 0 < L) (hρ : 0 ≤ ρ) (hρL : ρ * L < 2) (hε : 0 < ε)
    (hlip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    (hm : ∀ x, -(ρ / 2) * ‖F x‖ ^ 2 ≤ ⟪F x, x - z⟫) (hz : F z = 0)
    (x0 : E) (hR : ‖x0 - z‖ ≤ R) {K : ℕ}
    (hK : ⌊8 * L ^ 2 * R ^ 2 / ((margin L ρ) ^ 2 * ε ^ 2)⌋₊ + 1 ≤ K)
    (oracle : Oracle (E ⊕ E) (E × (E →L[ℝ] E))) (J : E → E →L[ℝ] E)
    (hF : ∀ k seed x, oracle.answer k (0, Sum.inl x) seed = (F x, 0))
    (hJ : ∀ k seed x, oracle.answer k (0, Sum.inr x) seed = (0, J x))
    (seed : (valueOnly L ρ ε x0).Seed) (ξ : (k : ℕ) → oracle.Seed k) :
    ‖F (execute oracle (valueOnly L ρ ε x0) (fun _ => K) seed ξ)‖ ≤ ε := by
  let G := fun x => L⁻¹ • F x
  let b := margin L ρ / 4
  have hb : 0 < b := by dsimp [b, margin]; linarith
  have hb' : b ≤ 1 / 4 := by dsimp [b, margin]; nlinarith [mul_nonneg hρ hL.le]
  have hnorm (x) : ‖G x‖ = ‖F x‖ / L := by
    simp only [G, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    ring
  have hGlip (x y) : ‖G x - G y‖ ≤ ‖x - y‖ := by
    dsimp [G]
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL),
      inv_mul_eq_div, div_le_iff₀ hL, mul_comm]
    exact hlip x y
  have hr (x) : ‖G x‖ ≤ ‖x - z‖ := by simpa [G, hz] using hGlip x z
  have hminty (x) : -(1 - 4 * b) * ‖G x‖ ^ 2 ≤ ⟪G x, x - z⟫ := by
    rw [hnorm]
    change _ ≤ ⟪L⁻¹ • F x, x - z⟫
    rw [real_inner_smul_left, inv_mul_eq_div, le_div_iff₀ hL]
    convert hm x using 1
    dsimp [b, margin]
    field_simp
    ring
  let V := fun s : E × E => potential b (s.1 - z) (G s.1) s.2
  let step := fun s : E × E => advance L ρ ε s (F s.1)
  let s := fun k : ℕ => step^[k] (x0, 0)
  let c := (4 * b) ^ 2 / 4 * (ε / L) ^ 2
  have inv (k : ℕ) : (∃ i < k, s k = s i ∧ ‖F (s i).1‖ ≤ ε) ∨
      V (s k) ≤ 2 * R ^ 2 - k * c := by
    induction k with
    | zero =>
      right
      rw [Nat.cast_zero]
      change potential b (x0 - z) (G x0) 0 ≤ 2 * R ^ 2 - 0 * c
      simp only [potential, smul_zero, add_zero, sub_zero, norm_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul]
      linarith [pow_le_pow_left₀ (norm_nonneg _) (hr x0) 2,
        pow_le_pow_left₀ (norm_nonneg _) hR 2]
    | succ k ih =>
      let y := (s k).1
      let h := (s k).2
      have hs : s (k + 1) = step (s k) := Function.iterate_succ_apply' ..
      by_cases ok : ‖F y‖ ≤ ε
      · refine Or.inl ⟨k, Nat.lt_succ_self k, ?_, ok⟩
        simp only [hs, step, advance, show ‖F (s k).1‖ ≤ ε from ok, ite_true]
      · have hi := ih.resolve_left (by
          rintro ⟨i, _, heq, hacc⟩
          exact ok (show ‖F (s k).1‖ ≤ ε by rw [heq]; exact hacc))
        right
        let y' := y - G y + (1 - b) • h
        have hnext : s (k + 1) = (y', G y) := by
          rw [hs]
          simp only [step, advance, show ¬ ‖F (s k).1‖ ≤ ε from ok, ite_false]
          rfl
        have hl : ‖G y' - G y‖ ≤ ‖(1 - b) • h - G y‖ := by
          convert hGlip y' y using 2
          dsimp [y']
          abel
        have hd := potential_step hb.le (y - z) (G y) h (G y') (hminty y) hl
        have hy : y' - z = (y - z) - G y + (1 - b) • h := by dsimp [y']; abel
        have he : ε / L ≤ ‖G y‖ := by rw [hnorm]; gcongr; exact (lt_of_not_ge ok).le
        have hc : c ≤ (4 * b) ^ 2 / 4 * ‖G y‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) he 2) (by positivity)
        rw [hnext]
        change potential b (y' - z) (G y') (G y) ≤ _
        rw [hy]
        change potential b (y - z) (G y) h ≤ _ at hi
        push_cast
        linarith [mul_nonneg (sq_nonneg b) (sq_nonneg ‖G y - h‖)]
  have hk : 8 * L ^ 2 * R ^ 2 / ((margin L ρ) ^ 2 * ε ^ 2) < (K : ℝ) := by
    apply (Nat.lt_floor_add_one _).trans_le
    exact_mod_cast hK
  have hc : 2 * R ^ 2 < K * c := by
    have hp : 0 < margin L ρ := WeakMintyHybrid.margin_pos hρL
    rw [div_lt_iff₀ (by positivity)] at hk
    dsimp [c, b]
    field_simp
    nlinarith
  obtain ⟨i, _, heq, hacc⟩ := (inv K).resolve_right (by
    have hn := potential_nonneg hb.le hb' (s K).2 (hr (s K).1) (hminty (s K).1)
    change 0 ≤ V (s K) at hn
    linarith)
  have horacle : ∀ k query seed, oracle.answer k (0, query) seed =
      WeakMintyHybrid.exactReply F J query := by
    intro k query seed
    cases query with
    | inl x => exact hF k seed x
    | inr x => exact hJ k seed x
  rw [execute_eq_of_answer_eq oracle _ horacle _ K seed ξ, execute_iterate]
  change ‖F (s K).1‖ ≤ ε
  rw [heq]
  exact hacc

end OracleTemplate.FullRangeWeakMintyFirstOrder
