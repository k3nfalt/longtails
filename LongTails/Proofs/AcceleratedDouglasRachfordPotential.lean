import LongTails.Proofs.DouglasRachfordEnvelope

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.DouglasRachford

open LongTails.Setups.DouglasRachfordSmoothConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma step_arith {γ L lam t s δ δp α β c n np : ℝ} (hγ : 0 < γ) (hL : 0 < L) (hlam0 : 0 < lam)
    (hlam : lam ≤ 1) (hstep : 4 * γ * L ≤ lam) (ht : 1 ≤ t) (hs : t * (t - 1) ≤ s) (hn : 0 ≤ n)
    (hc : 2 * c ≤ np + n) (hδp : γ / 2 * (1 - γ * L) * np ≤ δp)
    (hA : δ - δp ≤ α - lam * γ * c - γ / 2 * (np - 2 * c + n) + L * γ ^ 2 / 2 * (np + 2 * c + n))
    (hB : δ ≤ β - γ / 2 * (1 - γ * L) * n) :
    t ^ 2 * δ - t * ((t - 1) * α + β) + t ^ 2 * (lam * γ / 2) * n
        - ((t ^ 2 - 1 / 4) * (γ / 2 * (lam - 2 * γ * L)) + 1 / 4 * (γ / 2 * (1 - γ * L))) * n
      ≤ s * δp - (t * (t - 1) * (γ / 2 * (lam - 2 * γ * L))
          + (s - t * (t - 1)) * (γ / 2 * (1 - γ * L))) * np := by
  have ht0 : 0 ≤ t * (t - 1) := mul_nonneg (by linarith) (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hA ht0
  have h2 := mul_le_mul_of_nonneg_left hB (by linarith : (0 : ℝ) ≤ t)
  have h3 : 0 ≤ t * (t - 1) * (γ / 2 * (1 + L * γ - lam)) * (np + n - 2 * c) :=
    mul_nonneg (mul_nonneg ht0 (mul_nonneg (by linarith) (by nlinarith [mul_pos hγ hL])))
      (by linarith)
  have h4 : 0 ≤ (s - t * (t - 1)) * (δp - γ / 2 * (1 - γ * L) * np) :=
    mul_nonneg (by linarith) (by linarith)
  have hq : 0 ≤ 4 * t ^ 2 - t - 1 / 4 := by nlinarith
  have h5 : 0 ≤ n * (γ / 2) * ((lam / 4 - γ * L) * (4 * t ^ 2 - t - 1 / 4) + lam * t / 4
      + lam / 16 + (1 - lam) * t + (1 - lam) / 4) := by
    apply mul_nonneg (mul_nonneg hn (by linarith))
    have : 0 ≤ (lam / 4 - γ * L) * (4 * t ^ 2 - t - 1 / 4) := mul_nonneg (by linarith) hq
    have : 0 ≤ lam * t := mul_nonneg hlam0.le (by linarith)
    have : 0 ≤ (1 - lam) * t := mul_nonneg (by linarith) (by linarith)
    linarith
  nlinarith [h1, h2, h3, h4, h5]

lemma potential_step {γ L lam t s δ δp : ℝ} (hγ : 0 < γ) (hL : 0 < L) (hlam0 : 0 < lam)
    (hlam : lam ≤ 1) (hstep : 4 * γ * L ≤ lam) (ht : 1 ≤ t) (hs : t * (t - 1) ≤ s)
    {u w ws Gp G : E} (hδp : γ / 2 * (1 - γ * L) * ‖Gp‖ ^ 2 ≤ δp)
    (hA : δ - δp ≤ ⟪G, w - (u + (lam * γ) • Gp)⟫ - γ / 2 * ‖Gp - G‖ ^ 2
      + L * γ ^ 2 / 2 * ‖Gp + G‖ ^ 2)
    (hB : δ ≤ ⟪G, w - ws⟫ - γ / 2 * (1 - γ * L) * ‖G‖ ^ 2) :
    t ^ 2 * δ + ‖t • w - (t - 1) • u - (t * (lam * γ)) • G - ws‖ ^ 2 / (2 * (lam * γ))
        - ((t ^ 2 - 1 / 4) * (γ / 2 * (lam - 2 * γ * L)) + 1 / 4 * (γ / 2 * (1 - γ * L))) * ‖G‖ ^ 2
      ≤ s * δp + ‖t • w - (t - 1) • u - ws‖ ^ 2 / (2 * (lam * γ))
        - (t * (t - 1) * (γ / 2 * (lam - 2 * γ * L))
          + (s - t * (t - 1)) * (γ / 2 * (1 - γ * L))) * ‖Gp‖ ^ 2 := by
  have hlg : 0 < lam * γ := mul_pos hlam0 hγ
  have e1 : ⟪G, w - (u + (lam * γ) • Gp)⟫ = ⟪G, w - u⟫ - lam * γ * ⟪Gp, G⟫ := by
    rw [← sub_sub, inner_sub_right, real_inner_smul_right, real_inner_comm Gp G]
  have e2 : ‖Gp - G‖ ^ 2 = ‖Gp‖ ^ 2 - 2 * ⟪Gp, G⟫ + ‖G‖ ^ 2 := norm_sub_sq_real _ _
  have e3 : ‖Gp + G‖ ^ 2 = ‖Gp‖ ^ 2 + 2 * ⟪Gp, G⟫ + ‖G‖ ^ 2 := norm_add_sq_real _ _
  have e4 : ⟪G, t • w - (t - 1) • u - ws⟫ = (t - 1) * ⟪G, w - u⟫ + ⟪G, w - ws⟫ := by
    rw [show t • w - (t - 1) • u - ws = (t - 1) • (w - u) + (w - ws) by module, inner_add_right,
      real_inner_smul_right]
  have e5 : ‖t • w - (t - 1) • u - (t * (lam * γ)) • G - ws‖ ^ 2 =
      ‖t • w - (t - 1) • u - ws‖ ^ 2
        - 2 * (t * (lam * γ)) * ((t - 1) * ⟪G, w - u⟫ + ⟪G, w - ws⟫)
        + (t * (lam * γ)) ^ 2 * ‖G‖ ^ 2 := by
    rw [show t • w - (t - 1) • u - (t * (lam * γ)) • G - ws =
        (t • w - (t - 1) • u - ws) - (t * (lam * γ)) • G by abel, norm_sub_sq_real,
      real_inner_smul_right, real_inner_comm G, e4, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have e6 : (‖t • w - (t - 1) • u - ws‖ ^ 2
        - 2 * (t * (lam * γ)) * ((t - 1) * ⟪G, w - u⟫ + ⟪G, w - ws⟫)
        + (t * (lam * γ)) ^ 2 * ‖G‖ ^ 2) / (2 * (lam * γ)) =
      ‖t • w - (t - 1) • u - ws‖ ^ 2 / (2 * (lam * γ))
        - t * ((t - 1) * ⟪G, w - u⟫ + ⟪G, w - ws⟫) + t ^ 2 * (lam * γ / 2) * ‖G‖ ^ 2 := by
    field_simp
  have hc : 2 * ⟪Gp, G⟫ ≤ ‖Gp‖ ^ 2 + ‖G‖ ^ 2 := by
    have := sq_nonneg ‖Gp - G‖
    rw [e2] at this
    linarith
  rw [e1, e2, e3] at hA
  have key := step_arith hγ hL hlam0 hlam hstep ht hs (sq_nonneg ‖G‖) hc hδp hA hB
  rw [e5, e6]
  linarith

lemma first_step {γ L lam δ : ℝ} (hγ : 0 < γ) (hlam0 : 0 < lam) (hlam : lam ≤ 1)
    (hstep : 4 * γ * L ≤ lam) {w ws G : E}
    (hB : δ ≤ ⟪G, w - ws⟫ - γ / 2 * (1 - γ * L) * ‖G‖ ^ 2) :
    δ + ‖w - (lam * γ) • G - ws‖ ^ 2 / (2 * (lam * γ)) - γ / 2 * (1 - γ * L) * ‖G‖ ^ 2
      ≤ ‖w - ws‖ ^ 2 / (2 * (lam * γ)) := by
  have hlg : 0 < lam * γ := mul_pos hlam0 hγ
  have e5 : ‖w - (lam * γ) • G - ws‖ ^ 2 =
      ‖w - ws‖ ^ 2 - 2 * (lam * γ) * ⟪G, w - ws⟫ + (lam * γ) ^ 2 * ‖G‖ ^ 2 := by
    rw [show w - (lam * γ) • G - ws = (w - ws) - (lam * γ) • G by abel, norm_sub_sq_real,
      real_inner_smul_right, real_inner_comm G, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have e6 : (‖w - ws‖ ^ 2 - 2 * (lam * γ) * ⟪G, w - ws⟫ + (lam * γ) ^ 2 * ‖G‖ ^ 2)
      / (2 * (lam * γ)) =
      ‖w - ws‖ ^ 2 / (2 * (lam * γ)) - ⟪G, w - ws⟫ + lam * γ / 2 * ‖G‖ ^ 2 := by
    field_simp
  rw [e5, e6]
  have hn := sq_nonneg ‖G‖
  have h1 : 0 ≤ γ / 2 * (2 - lam - 2 * (γ * L)) * ‖G‖ ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) hn
  nlinarith [h1]

end OracleTemplate.DouglasRachford
