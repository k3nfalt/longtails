import LongTails.Proofs.StochasticQuasarEnvelope
import LongTails.Proofs.ConstrainedRegularization

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticQuasar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma regularized_upper_support {Q : Set E} {f : E → ℝ} {G : E → E} {L : ℝ}
    (hQ : Convex ℝ Q) (hG : ∀ y ∈ Q, HasGradientAt f (G y) y)
    (hlip : ∀ y ∈ Q, ∀ w ∈ Q, ‖G y - G w‖ ≤ L * ‖y - w‖)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) (c : E) :
    f y + L * ‖y - c‖ ^ 2 ≤ f x + L * ‖x - c‖ ^ 2 +
      ⟪G x + (2 * L) • (x - c), y - x⟫ + (3 * L) / 2 * ‖y - x‖ ^ 2 := by
  have hh := FrankWolfe.smooth_upper_bound_on hQ hG hlip hx hy
  have he : ‖y - c‖ ^ 2 = ‖x - c‖ ^ 2 + 2 * ⟪x - c, y - x⟫ + ‖y - x‖ ^ 2 := by
    rw [show y - c = (x - c) + (y - x) by abel, norm_add_sq_real]
  rw [he, inner_add_left, real_inner_smul_left]
  nlinarith

omit [CompleteSpace E] in
lemma projection_oracle_of_normal {Q : Set E} {P : E → E} (hP : ConstrainedMonotone.Proj Q P) :
    GeneralizedSliding.ProjectionOracle P Q := by
  intro y
  refine ⟨hP.mem y, ?_⟩
  intro u hu
  have hn := hP.var y u hu
  have he : ‖y - u‖ ^ 2 = ‖y - P y‖ ^ 2 - 2 * ⟪y - P y, u - P y⟫ + ‖u - P y‖ ^ 2 := by
    rw [show y - u = (y - P y) - (u - P y) by abel, norm_sub_sq_real]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith [sq_nonneg ‖u - P y‖]

lemma regularized_output_gap {Q : Set E} {P : E → E} {f : E → ℝ} {G : E → E}
    {L D : ℝ} (hP : ConstrainedMonotone.Proj Q P) (hL : 0 < L) (hQ : Convex ℝ Q)
    (hG : ∀ y ∈ Q, HasGradientAt f (G y) y)
    (hlip : ∀ y ∈ Q, ∀ w ∈ Q, ‖G y - G w‖ ≤ L * ‖y - w‖)
    (hD : ∀ y ∈ Q, ∀ w ∈ Q, ‖y - w‖ ≤ D) {x v : E} (hx : x ∈ Q) (hv : v ∈ Q)
    (c raw : E) :
    f (P (x - (1 / (3 * L)) • (raw + (2 * L) • (x - c)))) -
      (f v + L * ‖v - c‖ ^ 2) ≤ (3 * L) / 2 * ‖x - v‖ ^ 2 + D * ‖raw - G x‖ := by
  let F := fun y => f y + L * ‖y - c‖ ^ 2
  let g := G x + (2 * L) • (x - c)
  let e := raw - G x
  have hproj := projection_oracle_of_normal hP
  have hlo : F x + ⟪g, v - x⟫ ≤ F v := by
    have hh := regularized_lower_support hQ hG hlip hx hv c
    have hn : 0 ≤ L / 2 * ‖v - x‖ ^ 2 := by positivity
    dsimp only [F, g]
    linarith
  have hup : F (P (x - (1 / (3 * L)) • (g + e))) ≤ F x +
      ⟪g, P (x - (1 / (3 * L)) • (g + e)) - x⟫ +
      (3 * L) / 2 * ‖P (x - (1 / (3 * L)) • (g + e)) - x‖ ^ 2 :=
    regularized_upper_support hQ hG hlip hx (hP.mem _) c
  have hh := projected_cleanup_diameter hQ hproj hv (by positivity : 0 < 3 * L) hD hlo hup
  have he : g + e = raw + (2 * L) • (x - c) := by dsimp only [g, e]; abel
  rw [he] at hh
  have hn : 0 ≤ L * ‖P (x - (1 / (3 * L)) • (raw + (2 * L) • (x - c))) - c‖ ^ 2 := by positivity
  dsimp only [F, e] at hh
  linarith

lemma cleanup_accurate {Q : Set E} {P : E → E} {f : E → ℝ} {G : E → E}
    {L D ε : ℝ} (hP : ConstrainedMonotone.Proj Q P) (hL : 0 < L) (hD0 : 0 < D)
    (hε : 0 < ε) (hQ : Convex ℝ Q)
    (hG : ∀ y ∈ Q, HasGradientAt f (G y) y)
    (hlip : ∀ y ∈ Q, ∀ w ∈ Q, ‖G y - G w‖ ≤ L * ‖y - w‖)
    (hD : ∀ y ∈ Q, ∀ w ∈ Q, ‖y - w‖ ≤ D) {x v u c raw : E}
    (hx : x ∈ Q) (hv : v ∈ Q)
    (hprox : ‖x - v‖ ^ 2 ≤ ε / (12 * L))
    (hraw : ‖raw - G x‖ ≤ ε / (4 * D))
    (hgap : f v + L * ‖v - c‖ ^ 2 - f u ≤ ε / 8) :
    f (P (x - (1 / (3 * L)) • (raw + (2 * L) • (x - c)))) - f u ≤ ε := by
  have hh := regularized_output_gap hP hL hQ hG hlip hD hx hv c raw
  have hp := mul_le_mul_of_nonneg_left hprox (by positivity : 0 ≤ (3 * L) / 2)
  have hg := mul_le_mul_of_nonneg_left hraw hD0.le
  have he₁ : (3 * L) / 2 * (ε / (12 * L)) = ε / 8 := by field_simp; ring
  have he₂ : D * (ε / (4 * D)) = ε / 4 := by field_simp
  rw [he₁] at hp
  rw [he₂] at hg
  linarith

lemma initial_cleanup_accurate {Q : Set E} {P : E → E} {f : E → ℝ} {G : E → E}
    {L D ε : ℝ} (hP : ConstrainedMonotone.Proj Q P) (hL : 0 < L) (hD0 : 0 < D)
    (hQ : Convex ℝ Q)
    (hG : ∀ y ∈ Q, HasGradientAt f (G y) y)
    (hlip : ∀ y ∈ Q, ∀ w ∈ Q, ‖G y - G w‖ ≤ L * ‖y - w‖)
    (hD : ∀ y ∈ Q, ∀ w ∈ Q, ‖y - w‖ ≤ D) {x u raw : E}
    (hx : x ∈ Q) (hu : u ∈ Q) (he : 4 * L * D ^ 2 ≤ ε)
    (hraw : ‖raw - G x‖ ≤ ε / (4 * D)) :
    f (P (x - (1 / (3 * L)) • raw)) - f u ≤ ε := by
  have hh := regularized_output_gap hP hL hQ hG hlip hD hx hu x raw
  simp only [sub_self, smul_zero, add_zero, norm_sub_rev u x] at hh
  have hd := pow_le_pow_left₀ (norm_nonneg _) (hD x hx u hu) 2
  have hp := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 5 * L / 2)
  have hg := mul_le_mul_of_nonneg_left hraw hD0.le
  have he₂ : D * (ε / (4 * D)) = ε / 4 := by field_simp
  rw [he₂] at hg
  nlinarith [sq_nonneg D]

omit [CompleteSpace E] in
lemma projected_gradient_lipschitz {Q : Set E} {P G : E → E} {L : ℝ}
    (hP : ConstrainedMonotone.Proj Q P) (hL : 0 ≤ L)
    (hlip : ∀ y ∈ Q, ∀ w ∈ Q, ‖G y - G w‖ ≤ L * ‖y - w‖) :
    LipschitzWith L.toNNReal (fun x => G (P x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.coe_toNNReal _ hL, dist_eq_norm, dist_eq_norm]
  apply (hlip _ (hP.mem x) _ (hP.mem y)).trans
  apply mul_le_mul_of_nonneg_left _ hL
  have hh := hP.lipschitz.dist_le_mul x y
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using hh

lemma projected_objective_continuous {Q : Set E} {P : E → E} {f : E → ℝ} {G : E → E}
    (hP : ConstrainedMonotone.Proj Q P) (hG : ∀ y ∈ Q, HasGradientAt f (G y) y) :
    Continuous (fun x => f (P x)) := by
  have hc : ContinuousOn f Q := fun x hx => (hG x hx).continuousAt.continuousWithinAt
  exact hc.comp_continuous hP.lipschitz.continuous hP.mem

end OracleTemplate.StochasticQuasar
