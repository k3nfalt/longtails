import LongTails.Proofs.SplitBroxState

namespace OracleTemplate.SplitBrox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma pending_calls (M : Model E) {K : ℕ} {b R : ℝ} {s : State E}
    (hs : Invariant M K b R s) (hb : 0 < b) (hR : R ^ 2 ≤ (K : ℝ) * b ^ 2)
    (g : E) (cut : ℝ) (j : ℕ) (previous : E)
    (hp : s.phase = .local g cut j previous) : s.extra + j ≤ K := by
  have hc := hs.calls
  have he : (s.extra + j : ℝ) * b ^ 2 ≤ R ^ 2 := by
    by_cases hj : j = 0
    · subst j
      simp only [Nat.cast_zero, add_zero]
      nlinarith [sq_nonneg ‖s.momentum - M.xstar‖]
    · have hv := hs.phase_valid
      rw [hp] at hv
      have hd := hv.2.2.2
      simp only [hj, ite_false] at hd
      have hjc := mul_le_mul_of_nonneg_right (doublings_charge (j - 1)) (sq_nonneg b)
      have hj1 : j - 1 + 1 = j := by omega
      have hjreal : (j - 1 : ℕ) + (1 : ℝ) = j := by exact_mod_cast hj1
      rw [hjreal] at hjc
      simp only [radius, mul_pow] at hd
      nlinarith [sq_nonneg ‖previous - M.xstar‖]
  have heK := le_trans he hR
  have hsq : 0 < b ^ 2 := sq_pos_of_pos hb
  have hreal : (s.extra : ℝ) + (j : ℝ) ≤ K := (mul_le_mul_iff_left₀ hsq).mp heK
  exact_mod_cast hreal

lemma incomplete_rank (M : Model E) {K : ℕ} {b R : ℝ} {s : State E}
    (hs : Invariant M K b R s) (hb : 0 < b) (hR : R ^ 2 ≤ (K : ℝ) * b ^ 2)
    (hn : s.completed < K) : rank s < 3 * K := by
  cases hp : s.phase with
  | first =>
    have hc := hs.calls
    have he : (s.extra : ℝ) * b ^ 2 ≤ (K : ℝ) * b ^ 2 := by
      nlinarith [sq_nonneg ‖s.momentum - M.xstar‖]
    have hre : (s.extra : ℝ) ≤ K := (mul_le_mul_iff_left₀ (sq_pos_of_pos hb)).mp he
    have hen : s.extra ≤ K := by exact_mod_cast hre
    simp only [rank, hp]
    omega
  | «local» g cut j previous =>
    have hc := pending_calls M hs hb hR g cut j previous hp
    simp only [rank, hp]
    omega

def Matches (s : State E) (reply : Reply E) : Prop :=
  match s.phase, reply with
  | .first, .inl _ => True
  | .local _ _ _ _, .inr _ => True
  | _, _ => False

lemma rank_update {K : ℕ} {fstar : ℝ} {s : State E} {reply : Reply E}
    (hn : s.completed < K) (hm : Matches s reply) :
    rank s + 1 ≤ rank (update K fstar s reply) := by
  unfold update
  rw [ite_eq_right (by omega)]
  cases hp : s.phase with
  | first =>
    cases reply with
    | inl v =>
      obtain ⟨value, g⟩ := v
      dsimp only
      split_ifs <;> simp only [rank, hp] <;> omega
    | inr v => simp [Matches, hp] at hm
  | «local» g cut j previous =>
    cases reply with
    | inl v => simp [Matches, hp] at hm
    | inr v =>
      dsimp only
      split_ifs <;> simp only [rank, hp] <;> omega

end OracleTemplate.SplitBrox
