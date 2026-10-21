import LongTails.Proofs.LoraObjective
import LongTails.Proofs.SilverStability

namespace LongTails.Proofs.LoraSilverLocal

open LongTails.Algorithms.LoraGd LongTails.Proofs.LoraGeometry
open LongTails.Proofs.SilverCertificate
open scoped RealInnerProductSpace

lemma normalized_defect {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v gu gv : E) {fu fv L M : ℝ} (hL : 0 < L)
    (hh : ‖gu - gv‖ ^ 2 ≤ 2 * L * (fu - fv - ⟪gv, u - v⟫) +
      (L * M + 2 * M ^ 2) * ‖u - v‖ ^ 2) :
    -(M / L + 2 * M ^ 2 / L ^ 2) * ‖u - v‖ ^ 2 ≤
      defect (fu / L) (fv / L) u v ((1 / L) • gu) ((1 / L) • gv) := by
  have he : L ^ 2 * defect (fu / L) (fv / L) u v ((1 / L) • gu) ((1 / L) • gv) =
      2 * L * (fu - fv - ⟪gv, u - v⟫) - ‖gu - gv‖ ^ 2 := by
    simp only [defect, real_inner_smul_left, ← smul_sub, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp
  apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hL)).mp
  rw [he]
  have hn : L ^ 2 * (-(M / L + 2 * M ^ 2 / L ^ 2) * ‖u - v‖ ^ 2) =
      -(L * M + 2 * M ^ 2) * ‖u - v‖ ^ 2 := by
    field_simp
  rw [hn]
  linarith

lemma defect_coefficient {ρ R a : ℝ} (hρ : 0 < ρ) (hR : 0 < R)
    (ha : 0 ≤ a) (haR : a ≤ R) :
    (3 * ρ * R * a) / (8 * ρ * R ^ 2) +
      2 * (3 * ρ * R * a) ^ 2 / (8 * ρ * R ^ 2) ^ 2 ≤ a / R := by
  have hρ0 := ne_of_gt hρ
  have hR0 := ne_of_gt hR
  have he : (3 * ρ * R * a) / (8 * ρ * R ^ 2) +
      2 * (3 * ρ * R * a) ^ 2 / (8 * ρ * R ^ 2) ^ 2 =
      3 * a / (8 * R) + 9 * a ^ 2 / (32 * R ^ 2) := by field_simp; ring
  rw [he]
  apply (mul_le_mul_iff_of_pos_left (show 0 < 32 * R ^ 2 by positivity)).mp
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left haR ha]

lemma outer_gradient_tube {m n r : ℕ} (v z : Factors m n r)
    (G : MatrixSpace m n → MatrixSpace m n) {ρ R a : ℝ}
    (hρ : 0 ≤ ρ) (hR : 0 ≤ R) (ha : 0 ≤ a) (haR : a ≤ R)
    (hz : ∀ h, ‖linearization z h‖ ≤ 2 * R * ‖h‖)
    (hv : ‖v - z‖ ≤ a) (hzero : G (product z) = 0)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ ρ * ‖x - y‖) :
    ‖G (product v)‖ ≤ 3 * ρ * R * a := by
  have hp := product_local_bound v z hz
  have hscale := mul_le_mul_of_nonneg_left hv (show 0 ≤ 2 * R by positivity)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hv 2
  have ha2 := mul_le_mul_of_nonneg_left haR ha
  have hp' : ‖product v - product z‖ ≤ 3 * R * a := by nlinarith
  have hh := hlip (product v) (product z)
  rw [hzero, sub_zero] at hh
  have hscaled := mul_le_mul_of_nonneg_left hp' hρ
  nlinarith

lemma pullback_defect {m n r : ℕ} (u v z : Factors m n r)
    {f : MatrixSpace m n → ℝ} {G : MatrixSpace m n → MatrixSpace m n} {ρ R a : ℝ}
    (hρ : 0 < ρ) (hR : 0 < R) (ha : 0 ≤ a) (haR : a ≤ R)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ X, HasGradientAt f (G X) X)
    (hlip : ∀ X Y, ‖G X - G Y‖ ≤ ρ * ‖X - Y‖)
    (huD : ∀ h, ‖linearization u h‖ ≤ 2 * R * ‖h‖)
    (hzD : ∀ h, ‖linearization z h‖ ≤ 2 * R * ‖h‖)
    (hv : ‖v - z‖ ≤ a) (hzero : G (product z) = 0) :
    -(a / R) * ‖u - v‖ ^ 2 ≤
      defect (f (product u) / (8 * ρ * R ^ 2)) (f (product v) / (8 * ρ * R ^ 2)) u v
        ((1 / (8 * ρ * R ^ 2)) • pullback u (G (product u)))
        ((1 / (8 * ρ * R ^ 2)) • pullback v (G (product v))) := by
  have hDu : ‖derivative u‖ ≤ 2 * R :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) huD
  have hM := outer_gradient_tube v z G (le_of_lt hρ) (le_of_lt hR) ha haR hzD hv hzero hlip
  have hi := LongTails.Proofs.LoraLocalInterpolation.pullback_interpolation hρ hc hg hlip
    product u v (derivative u) (derivative v) hDu (derivative_difference_norm u v)
    hM (remainder_norm u v)
  rw [← pullback_adjoint, ← pullback_adjoint] at hi
  have hraw : ‖pullback u (G (product u)) - pullback v (G (product v))‖ ^ 2 ≤
      2 * (8 * ρ * R ^ 2) *
        (f (product u) - f (product v) - ⟪pullback v (G (product v)), u - v⟫) +
      ((8 * ρ * R ^ 2) * (3 * ρ * R * a) + 2 * (3 * ρ * R * a) ^ 2) * ‖u - v‖ ^ 2 := by
    nlinarith only [hi]
  have hn := normalized_defect u v (pullback u (G (product u))) (pullback v (G (product v)))
    (show 0 < 8 * ρ * R ^ 2 by positivity) hraw
  have hcoef := mul_le_mul_of_nonneg_right (defect_coefficient hρ hR ha haR)
    (sq_nonneg ‖u - v‖)
  linarith

lemma block {m n r : ℕ} (x z c : Factors m n r)
    {f : MatrixSpace m n → ℝ} {G : MatrixSpace m n → MatrixSpace m n}
    {ρ R s a D : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hs : 0 ≤ s) (hsR : s ≤ R)
    (ha : 0 ≤ a) (haR : a ≤ R) (hD : 0 ≤ D)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ X, HasGradientAt f (G X) X)
    (hlip : ∀ X Y, ‖G X - G Y‖ ≤ ρ * ‖X - Y‖)
    (href : ∀ h, ‖linearization c h‖ ≤ R * ‖h‖)
    (hzero : G (product c) = 0) (hmin : ∀ X, f (product c) ≤ f X)
    (hzprod : product z = product c) (hcenter : ‖z - c‖ + a ≤ s / 2)
    (hx : ‖x - z‖ ≤ D) (k : ℕ)
    (hsize : (3 : ℝ) ^ k * (5 * D) ≤ 2 * a + 3 * D)
    (herror : 12 * (a / R) * (2 + 2 * LongTails.Algorithms.SilverSchedule.ratio) ^ k * a ^ 2 ≤ D ^ 2) :
    let L := 8 * ρ * R ^ 2
    let F := fun u => f (product u) / L
    let g := fun u => (1 / L) • pullback u (G (product u))
    (∀ u ∈ LongTails.Proofs.SilverTrace.nodes g (LongTails.Algorithms.SilverSchedule.steps k) x,
      ‖u - z‖ ≤ a) ∧
    ‖LongTails.Algorithms.SilverSchedule.run g (LongTails.Algorithms.SilverSchedule.steps k) x - z‖ ^ 2 +
      2 * (LongTails.Algorithms.SilverSchedule.steps k).sum *
        (F (LongTails.Algorithms.SilverSchedule.run g (LongTails.Algorithms.SilverSchedule.steps k) x) - F z) ≤
          2 * D ^ 2 := by
  intro L F g
  have hL : 0 < L := by dsimp [L]; positivity
  have hzref : ‖z - c‖ ≤ s / 2 := by linarith
  have hzG : G (product z) = 0 := by rw [hzprod, hzero]
  have hzpull : pullback z (G (product z)) = 0 := by rw [pullback_adjoint, hzG, map_zero]
  have hzgrad : g z = 0 := by simp only [g, hzpull, smul_zero]
  have hin : ∀ u, ‖u - z‖ ≤ a → ‖u - c‖ ≤ s / 2 := by
    intro u hu
    have hh : ‖u - c‖ ≤ ‖u - z‖ + ‖z - c‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (u - z) (z - c)
    linarith
  have hDbound : ∀ u, ‖u - c‖ ≤ s / 2 → ∀ h, ‖linearization u h‖ ≤ 2 * R * ‖h‖ := by
    intro u hu h
    have hh : ‖derivative u‖ ≤ 2 * R :=
      (derivative_local_bound u c href (le_of_lt hR) hu).trans (by linarith)
    exact ((derivative u).le_opNorm h).trans (mul_le_mul_of_nonneg_right hh (norm_nonneg h))
  have hnonneg : ∀ u, ‖u - z‖ ≤ a → 0 ≤ F u - F z := by
    intro u _
    change 0 ≤ f (product u) / L - f (product z) / L
    rw [← sub_div, hzprod]
    exact div_nonneg (sub_nonneg.mpr (hmin _)) (le_of_lt hL)
  have hgrad : ∀ u, ‖u - z‖ ≤ a → ‖g u‖ ≤ ‖u - z‖ := by
    intro u hu
    have hh := LongTails.Proofs.LoraObjective.objective_lipschitz_ball u z c G
      (le_of_lt hρ) (le_of_lt hR) hs hsR href (hin u hu) hzref hzero hlip
    rw [hzpull, sub_zero] at hh
    change ‖(1 / L) • pullback u (G (product u))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hL)]
    have hb := mul_le_mul_of_nonneg_left hh (le_of_lt (one_div_pos.mpr hL))
    change (1 / L) * ‖pullback u (G (product u))‖ ≤ (1 / L) * (L * ‖u - z‖) at hb
    simpa only [one_div, inv_mul_cancel_left₀ (ne_of_gt hL)] using hb
  have hq : ∀ u v, ‖u - z‖ ≤ a → ‖v - z‖ ≤ a →
      -(a / R) * ‖u - v‖ ^ 2 ≤ defect (F u) (F v) u v (g u) (g v) := by
    intro u v hu hv
    exact pullback_defect u v z hρ hR ha haR hc hg hlip
      (hDbound u (hin u hu)) (hDbound z hzref) hv hzG
  obtain ⟨hnodes, henergy⟩ := LongTails.Proofs.SilverStability.local_block F g x z ha hD
    (div_nonneg ha (le_of_lt hR)) hzgrad hx hnonneg hgrad hq k hsize herror
  refine ⟨hnodes, ?_⟩
  have hS : 0 ≤ (LongTails.Algorithms.SilverSchedule.steps k).sum :=
    List.sum_nonneg (fun h hh => le_of_lt (steps_positive k h hh))
  have hp : 0 ≤ (LongTails.Algorithms.SilverSchedule.steps k).sum *
      ((LongTails.Algorithms.SilverSchedule.steps k).sum + 1) *
      ‖g (LongTails.Algorithms.SilverSchedule.run g (LongTails.Algorithms.SilverSchedule.steps k) x)‖ ^ 2 := by
    positivity
  linarith

end LongTails.Proofs.LoraSilverLocal
