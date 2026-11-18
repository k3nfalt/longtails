import LongTails.Setups.HolderNoiseNonconvexLower
import LongTails.Proofs.HolderNoiseHardScaling

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

namespace LongTails.Proofs.HolderNoiseHardAdmissible

open HolderNoiseHardScaling HolderNoiseHardOracle QuasarCoinLaw
open LongTails.Setups.HolderNoiseNonconvexLower

noncomputable def pairOracle (q : LowerParams) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (g : EuclideanSpace ℝ (Fin q.d) → Bool → EuclideanSpace ℝ (Fin q.d)) :
    OracleTemplate.Oracle (EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d))
      (EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d)) 1 where
  Seed := fun _ => Bool
  law := coinPath p hp hp1
  answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω)

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace in
lemma field_measurable {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (x0 : EuclideanSpace ℝ (Fin d)) : Measurable (field π a b x0) := by
  have hl : LipschitzWith ⟨2200 * a / b ^ 2, by positivity⟩ (field π a b x0) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simp only [dist_eq_norm]
      exact field_lipschitz π ha hb x0 x y
  exact hl.continuous.measurable

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace in
lemma noise_measurable {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (x0 : EuclideanSpace ℝ (Fin d)) : Measurable (noise π a b x0) := by
  have hl : LipschitzWith ⟨10242 * a / b ^ 2, by positivity⟩ (noise π a b x0) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simp only [dist_eq_norm]
      exact noise_lipschitz π ha hb x0 x y
  exact hl.continuous.measurable

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace in
lemma oracle_measurable {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (x0 : EuclideanSpace ℝ (Fin d)) (p : ℝ) :
    Measurable (Function.uncurry (oracleValue p (field π a b x0) (noise π a b x0))) := by
  exact ((field_measurable π ha hb x0).comp measurable_fst).add
    (((measurable_of_countable (coinError p)).comp measurable_snd).smul
      ((noise_measurable π ha hb x0).comp measurable_fst))

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace in
lemma admissible (q : LowerParams) {k : ℕ} (π : Fin (k + 1) ↪ Fin q.d)
    {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hp : 0 < p) (hp1 : p ≤ 1)
    (hν : 0 ≤ q.ν) (hν1 : q.ν ≤ 1) (hM0 : 0 ≤ q.M)
    (hL : 2200 * a / b ^ 2 ≤ q.L) (hΔ : 8 * a * (k + 1) ≤ q.Δ)
    (hσ : p = 1 ∨ (66 * a / b) ^ 2 / p ≤ q.σ ^ 2)
    (hM : p = 1 ∨ ((2 * (66 * a / b)) ^ (2 - 2 * q.ν) * (10242 * a / b ^ 2) ^ (2 * q.ν) / p) ≤ q.M) :
    spec.admissible q (objective π a b q.x0)
      (pairOracle q hp.le hp1 (oracleValue p (field π a b q.x0) (noise π a b q.x0))) := by
  dsimp only [spec, LongTails.Setups.HolderNoiseNonconvex.spec, LowerParams.toParams]
  have hg (x : EuclideanSpace ℝ (Fin q.d)) : gradient (objective π a b q.x0) x = field π a b q.x0 x :=
    (objective_gradient π a b q.x0 x).gradient
  refine ⟨oracleValue p (field π a b q.x0) (noise π a b q.x0), coinLaw p hp.le hp1,
    coinPath p hp.le hp1, coinPath_iid hp.le hp1, rfl, ?_, ?_, ?_, oracle_measurable π ha hb q.x0 p,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hg]
    exact objective_gradient π a b q.x0 x
  · intro x y
    rw [hg, hg]
    exact (field_lipschitz π ha hb q.x0 x y).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  · intro x
    exact (objective_gap π ha b q.x0 x).trans hΔ
  · intro x
    exact Integrable.of_finite
  · intro x
    rw [hg]
    exact oracle_unbiased hp hp1 _ _ x
  · intro x
    exact Integrable.of_finite
  · intro x
    rw [hg]
    rcases hσ with rfl | hσ
    · rw [oracle_variance hp hp1]
      simp only [sub_self, zero_div, zero_mul]
      positivity
    · exact (oracle_variance_le hp hp1 _ _ x (noise_norm π ha hb q.x0 x)).trans hσ
  · intro x y
    exact Integrable.of_finite
  · intro x y
    rw [hg, hg]
    rcases hM with rfl | hM
    · rw [oracle_increment hp hp1]
      simp only [sub_self, zero_div, zero_mul]
      exact mul_nonneg hM0 (Real.rpow_nonneg (norm_nonneg _) _)
    · exact (oracle_holder hp hp1 (by positivity) hν hν1 _ _
        (noise_norm π ha hb q.x0) (noise_lipschitz π ha hb q.x0) x y).trans
        (mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg (norm_nonneg _) _))

end LongTails.Proofs.HolderNoiseHardAdmissible
