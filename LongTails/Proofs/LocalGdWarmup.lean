import LongTails.Proofs.GdConvex

namespace LongTails.Proofs.LocalGdWarmup

lemma step_length {e e' g L α : ℝ} (hL : 0 < L) (hα : 0 < α)
    (he : 0 ≤ e) (he' : 0 ≤ e') (hg : 0 ≤ g)
    (hdec : e' ≤ e - g ^ 2 / (2 * L)) (hdom : α * e ≤ 2 * g ^ 2) :
    g / L ≤ 4 * Real.sqrt (2 / α) * (Real.sqrt e - Real.sqrt e') := by
  have hroot := Real.sq_sqrt he
  have hroot' := Real.sq_sqrt he'
  have hc := Real.sq_sqrt (show 0 ≤ 2 / α by positivity)
  have hc0 := Real.sqrt_nonneg (2 / α)
  have hee : e' ≤ e := by
    have hh : 0 ≤ g ^ 2 / (2 * L) := by positivity
    linarith
  have hd : 0 ≤ Real.sqrt e - Real.sqrt e' := sub_nonneg.mpr (Real.sqrt_le_sqrt hee)
  have hdom' : e ≤ (2 / α) * g ^ 2 := by
    apply (mul_le_mul_iff_of_pos_left hα).mp
    field_simp
    nlinarith
  have hrootbound : Real.sqrt e ≤ Real.sqrt (2 / α) * g := by
    nlinarith [mul_nonneg hc0 hg, Real.sqrt_nonneg e]
  have hdrop : g ^ 2 ≤ 2 * L * (e - e') := by
    have hh : g ^ 2 / (2 * L) ≤ e - e' := by linarith
    have hh' := (div_le_iff₀ (show 0 < 2 * L by positivity)).mp hh
    nlinarith
  have hdiff : e - e' ≤ 2 * (Real.sqrt e - Real.sqrt e') * Real.sqrt e := by
    nlinarith [sq_nonneg (Real.sqrt e - Real.sqrt e')]
  have hdiff' := mul_le_mul_of_nonneg_left hdiff (show 0 ≤ 2 * L by positivity)
  have hscale := mul_le_mul_of_nonneg_left hrootbound
    (show 0 ≤ 4 * L * (Real.sqrt e - Real.sqrt e') by positivity)
  have hgcap : g ≤ 4 * L * Real.sqrt (2 / α) * (Real.sqrt e - Real.sqrt e') := by
    by_cases hz : g = 0
    · rw [hz]
      positivity
    · have hgp : 0 < g := lt_of_le_of_ne hg (Ne.symm hz)
      nlinarith
  exact (div_le_iff₀ hL).mpr (by nlinarith only [hgcap])

lemma trajectory_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E → ℝ) (g : E → E) (x : ℕ → E) (c : E) {L α e₀ r : ℝ}
    (hL : 0 < L) (hα : 0 < α) (hαL : α ≤ 4 * L) (he₀ : 0 ≤ e₀)
    (heinit : e (x 0) = e₀)
    (hroom : ‖x 0 - c‖ + 4 * Real.sqrt (2 / α) * Real.sqrt e₀ ≤ r)
    (hupdate : ∀ k, x (k + 1) = x k - (1 / L) • g (x k))
    (hstep : ∀ u, ‖u - c‖ ≤ r → e u ≤ e₀ →
      0 ≤ e (u - (1 / L) • g u) ∧
      e (u - (1 / L) • g u) ≤ e u - ‖g u‖ ^ 2 / (2 * L) ∧
      α * e u ≤ 2 * ‖g u‖ ^ 2) :
    ∀ k, 0 ≤ e (x k) ∧ e (x k) ≤ e₀ * (1 - α / (4 * L)) ^ k ∧
      ‖x k - x 0‖ ≤ 4 * Real.sqrt (2 / α) * (Real.sqrt e₀ - Real.sqrt (e (x k))) := by
  have hq : 0 ≤ 1 - α / (4 * L) := by
    have hh := (div_le_one (show 0 < 4 * L by positivity)).mpr hαL
    linarith
  have hq1 : 1 - α / (4 * L) ≤ 1 := by
    have hh : 0 ≤ α / (4 * L) := by positivity
    linarith
  have hC : 0 ≤ 4 * Real.sqrt (2 / α) := by positivity
  intro k
  induction k with
  | zero => simp only [heinit, pow_zero, mul_one, sub_self, norm_zero, mul_zero, le_refl, and_true]; exact he₀
  | succ k ih =>
    have hcap : e (x k) ≤ e₀ := ih.2.1.trans
      (by simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hq hq1 : (1 - α / (4 * L)) ^ k ≤ 1) he₀)
    have hcurrent : ‖x k - c‖ ≤ r := by
      have hn : ‖x k - c‖ ≤ ‖x k - x 0‖ + ‖x 0 - c‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le (x k - x 0) (x 0 - c)
      have hh := mul_nonneg hC (Real.sqrt_nonneg (e (x k)))
      nlinarith [ih.2.2]
    obtain ⟨hnext, hdec, hdom⟩ := hstep (x k) hcurrent hcap
    rw [← hupdate k] at hnext hdec
    have hlength := step_length hL hα ih.1 hnext (norm_nonneg (g (x k))) hdec hdom
    have hcon : e (x (k + 1)) ≤ (1 - α / (4 * L)) * e (x k) := by
      have hh : α * e (x k) / (4 * L) ≤ ‖g (x k)‖ ^ 2 / (2 * L) := by
        apply (div_le_div_iff₀ (show 0 < 4 * L by positivity) (show 0 < 2 * L by positivity)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hdom (show 0 ≤ 2 * L by positivity)]
      rw [show α * e (x k) / (4 * L) = (α / (4 * L)) * e (x k) by ring] at hh
      nlinarith
    refine ⟨hnext, ?_, ?_⟩
    · have hh := mul_le_mul_of_nonneg_left ih.2.1 hq
      rw [pow_succ]
      nlinarith
    · have hdist : ‖x (k + 1) - x k‖ = ‖g (x k)‖ / L := by
        rw [hupdate, sub_sub_cancel_left, norm_neg, norm_smul,
          Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hL)]
        ring
      have hn : ‖x (k + 1) - x 0‖ ≤ ‖x (k + 1) - x k‖ + ‖x k - x 0‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le (x (k + 1) - x k) (x k - x 0)
      rw [hdist] at hn
      nlinarith [ih.2.2]

end LongTails.Proofs.LocalGdWarmup
