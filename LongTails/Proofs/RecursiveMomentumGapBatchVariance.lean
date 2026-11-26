import LongTails.Proofs.RecursiveMomentumConvergence

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.RecursiveMomentumGapBatch

open RecursiveMomentum NormalizedStorm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {F : E → ℝ} {g : E → Ω → E} {L Lbar Γ Λ lower : ℝ}

omit [IsProbabilityMeasure p] [BorelSpace E] [SecondCountableTopology E] in
private lemma nearby (H : AffineHyp p F g L Lbar Γ Λ lower) (x : E) {h : ℝ} (hh : 0 < h) :
    ∃ y, ‖gradient F y‖ ≤ h ∧ ‖x - y‖ * h ≤ 2 * (F x - lower) := by
  have hL := H.L_pos
  let d := h ^ 2 / (2 * L)
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt ((F x - lower) / d)
  suffices aux : ∀ (k : ℕ) (u : E), F u - lower < k * d →
      ∃ y, ‖gradient F y‖ ≤ h ∧ ‖u - y‖ * h ≤ 2 * (F u - lower) from
    aux n x ((div_lt_iff₀ hd).mp hn)
  intro k
  induction k with
  | zero => intro u hu; simp at hu; linarith [H.low u]
  | succ k ih =>
    intro u hu
    by_cases hg : ‖gradient F u‖ ≤ h
    · exact ⟨u, hg, by simp only [sub_self, norm_zero, zero_mul]; linarith [H.low u]⟩
    let v := u - (1 / L) • gradient F u
    have hs : F v ≤ F u - ‖gradient F u‖ ^ 2 / (2 * L) := Gradient.descent hL H.grad H.lip u
    have hdec : d ≤ ‖gradient F u‖ ^ 2 / (2 * L) := by dsimp [d]; gcongr; linarith
    push_cast at hu
    obtain ⟨y, hy, hy'⟩ := ih v (by linarith)
    refine ⟨y, hy, ?_⟩
    have ht := mul_le_mul_of_nonneg_right (dist_triangle u v y) hh.le
    simp only [dist_eq_norm] at ht
    have huv : ‖u - v‖ = ‖gradient F u‖ / L := by
      simp [v, norm_smul, abs_of_pos hL, div_eq_inv_mul]
    rw [huv] at ht
    have hstep : ‖gradient F u‖ / L * h ≤ 2 * (‖gradient F u‖ ^ 2 / (2 * L)) := by
      field_simp
      nlinarith [mul_nonneg (norm_nonneg (gradient F u)) (sub_nonneg.mpr (le_of_not_ge hg))]
    linarith

omit [BorelSpace E] [SecondCountableTopology E] in
private lemma transfer (H : AffineHyp p F g L Lbar Γ Λ lower) (x y : E) :
    ∫ ω, ‖g x ω - gradient F x‖ ^ 2 ∂p ≤
      2 * (Γ ^ 2 * ‖gradient F y‖ ^ 2 + Λ ^ 2) +
      4 * (Lbar ^ 2 + L ^ 2) * ‖x - y‖ ^ 2 := by
  have hm := integral_mono (H.var_int x)
    (((H.var_int y).const_mul 2).add (((H.diff_int x y).const_mul 4).add
      (integrable_const (4 * ‖gradient F x - gradient F y‖ ^ 2)))) (fun ω => by
      change ‖g x ω - gradient F x‖ ^ 2 ≤ 2 * ‖g y ω - gradient F y‖ ^ 2 +
        (4 * ‖g x ω - g y ω‖ ^ 2 + 4 * ‖gradient F x - gradient F y‖ ^ 2)
      have e : g x ω - gradient F x = (g y ω - gradient F y) +
          ((g x ω - g y ω) + -(gradient F x - gradient F y)) := by abel
      rw [e]
      have h₁ := sq_norm_add_le (g y ω - gradient F y)
        ((g x ω - g y ω) + -(gradient F x - gradient F y))
      have h₂ := sq_norm_add_le (g x ω - g y ω) (-(gradient F x - gradient F y))
      rw [norm_neg] at h₂
      linarith)
  simp only [Pi.add_apply] at hm
  rw [integral_add (g := fun ω => 4 * ‖g x ω - g y ω‖ ^ 2 + 4 * ‖gradient F x - gradient F y‖ ^ 2) ((H.var_int y).const_mul 2) (((H.diff_int x y).const_mul _).add (integrable_const _)),
    integral_add ((H.diff_int x y).const_mul 4) (integrable_const _), integral_const_mul,
    integral_const_mul, integral_const, probReal_univ, one_smul] at hm
  have hl := H.lip x y
  have hs := pow_le_pow_left₀ (norm_nonneg _) hl 2
  nlinarith [H.var y, H.mss x y]

omit [BorelSpace E] [SecondCountableTopology E] in
lemma variance_gap (H : AffineHyp p F g L Lbar Γ Λ lower) (hl : 0 ≤ Lbar) (hg : 0 ≤ Γ) (x : E) :
    ∫ ω, ‖g x ω - gradient F x‖ ^ 2 ∂p ≤
      2 * Λ ^ 2 + 12 * Γ * (L + Lbar) * (F x - lower) := by
  let D := F x - lower
  let S := L + Lbar
  have hS : 0 < S := by dsimp [S]; linarith [H.L_pos]
  have hD : 0 ≤ D := sub_nonneg.mpr (H.low x)
  change _ ≤ 2 * Λ ^ 2 + 12 * Γ * S * D
  rcases hg.eq_or_lt with h | hg
  · subst Γ; nlinarith [H.var x, sq_nonneg Λ]
  rcases hD.eq_or_lt with h | hD
  · have h0 : ‖gradient F x‖ ^ 2 ≤ 0 := by
      have hs : ‖gradient F x‖ ^ 2 ≤ 2 * L * D := H.grad_sq_le x
      simpa [← h] using hs
    have := mul_le_mul_of_nonneg_left h0 (sq_nonneg Γ)
    rw [← h]; nlinarith [H.var x, sq_nonneg Λ]
  let t := Real.sqrt (4 * S * D / Γ)
  have ht : 0 < t := Real.sqrt_pos.2 (by positivity)
  have ht2 : t ^ 2 = 4 * S * D / Γ := Real.sq_sqrt (by positivity)
  obtain ⟨y, hy, hd⟩ := nearby H x ht
  change ‖x - y‖ * t ≤ 2 * D at hd
  have ha := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy 2) (sq_nonneg Γ)
  have hb := pow_le_pow_left₀ (by positivity : 0 ≤ ‖x - y‖ * t) hd 2
  rw [mul_pow, ht2] at hb
  have hb' : S * ‖x - y‖ ^ 2 ≤ Γ * D := by
    have hh := mul_le_mul_of_nonneg_right hb hg.le
    field_simp at hh
    nlinarith
  have hc := mul_le_mul_of_nonneg_left hb' hS.le
  have he : Γ ^ 2 * t ^ 2 = 4 * Γ * S * D := by rw [ht2]; field_simp
  have hf : Lbar ^ 2 + L ^ 2 ≤ S ^ 2 := by dsimp [S]; nlinarith [H.L_pos]
  have := mul_le_mul_of_nonneg_right hf (sq_nonneg ‖x - y‖)
  nlinarith [transfer H x y]

omit [BorelSpace E] [SecondCountableTopology E] in
lemma abcHyp (H : AffineHyp p F g L Lbar Γ Λ lower) (hl : 0 ≤ Lbar) (hg : 0 ≤ Γ) :
    Hyp p F g (L + Lbar) (6 * Γ * (L + Lbar)) (2 * Λ ^ 2) lower := by
  have hL := H.L_pos
  refine ⟨H.grad, fun x y => (H.lip x y).trans ?_, H.meas, H.int, H.mean, H.var_int,
    H.diff_int, fun x y => (H.mss x y).trans ?_, H.low, fun x => ?_, by linarith,
    by positivity, by positivity⟩
  · gcongr; linarith
  · gcongr; linarith
  · linarith [variance_gap H hl hg x]

end OracleTemplate.RecursiveMomentumGapBatch
