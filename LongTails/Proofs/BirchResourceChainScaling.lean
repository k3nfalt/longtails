import LongTails.Proofs.BirchResourceChainOracle
import LongTails.Proofs.BirchResourceGeometry

namespace LongTails.Proofs.BirchResourceChain

open OracleTemplate.Rennala (Point)
open LongTails.Proofs.BirchResourceGeometry
open LongTails.Setups.UscgConstant (dualNorm)

noncomputable def scaledObjective {D : ℕ} (a s : ℝ) (x : Point D) : ℝ :=
  (a * s) * objective (a⁻¹ • x)

noncomputable def scaledOracle {D : ℕ} (a s p : ℝ) (x : Point D) (b : Bool) : Point D :=
  s • noisyGradient p (a⁻¹ • x) b

lemma scaled_gradient {D : ℕ} {a : ℝ} (ha : 0 < a) (s : ℝ) (x : Point D) :
    HasGradientAt (scaledObjective a s) (s • gradient objective (a⁻¹ • x)) x := by
  let z := a⁻¹ • x
  have hz := ((objective_diff D z).hasGradientAt).hasFDerivAt
  have hx := (hasFDerivAt_id (𝕜 := ℝ) x).const_smul (a⁻¹)
  have h := (hz.comp x hx).const_mul (a * s)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro y
    simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
      InnerProductSpace.toDual_apply_apply, real_inner_smul_left, inner_smul_right, smul_eq_mul]
    dsimp only [z]
    field_simp

lemma scaled_grad_value {D : ℕ} {a : ℝ} (ha : 0 < a) (s : ℝ) (x : Point D) :
    gradient (scaledObjective a s) x = s • gradient objective (a⁻¹ • x) :=
  (scaled_gradient ha s x).gradient

lemma scaled_smooth {D : ℕ} {L s : ℝ} (hL : 0 < L) (hs : 0 < s) (x y : Point D) :
    let a := 30 * s / L
    ‖gradient (scaledObjective a s) x - gradient (scaledObjective a s) y‖ ≤ L * ‖x - y‖ := by
  let a := 30 * s / L
  have ha : 0 < a := by dsimp [a]; positivity
  change ‖gradient (scaledObjective a s) x - gradient (scaledObjective a s) y‖ ≤ L * ‖x - y‖
  rw [scaled_grad_value ha s x, scaled_grad_value ha s y, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos hs]
  refine (mul_le_mul_of_nonneg_left (objective_smooth (a⁻¹ • x) (a⁻¹ • y)) hs.le).trans_eq ?_
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
  dsimp [a]
  field_simp

lemma scaled_gap {D : ℕ} {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hD : 0 < D) (x : Point D) :
    scaledObjective a s (0 : Point D) - scaledObjective a s x ≤ (a * s) * (4 * D) := by
  unfold scaledObjective
  rw [smul_zero, ← mul_sub]
  exact mul_le_mul_of_nonneg_left (gap hD _) (mul_nonneg ha hs)

lemma scaled_mean {D : ℕ} {a p : ℝ} (ha : 0 < a) (hp : 0 < p) (s : ℝ) (x : Point D) :
    (1 - p) • scaledOracle a s p x false + p • scaledOracle a s p x true =
      gradient (scaledObjective a s) x := by
  rw [scaled_grad_value ha]
  unfold scaledOracle
  have h := congrArg (fun v : Point D => s • v) (noisy_mean hp (a⁻¹ • x))
  simpa only [smul_add, smul_comm s] using h

lemma scaled_variance {D : ℕ} {a p s : ℝ} (ha : 0 < a) (hp : 0 < p) (hp' : p ≤ 1)
    (x : Point D) :
    (1 - p) * ‖scaledOracle a s p x false - gradient (scaledObjective a s) x‖ ^ 2 +
      p * ‖scaledOracle a s p x true - gradient (scaledObjective a s) x‖ ^ 2 ≤
        s ^ 2 * ((1 - p) / p) := by
  rw [scaled_grad_value ha]
  unfold scaledOracle
  simp only [← smul_sub, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h := mul_le_mul_of_nonneg_left (noisy_variance hp hp' (a⁻¹ • x)) (sq_nonneg s)
  convert h using 1; ring

lemma scaled_unrevealed {D : ℕ} {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (N : Seminorm ℝ (Point D)) (hN : ∀ v, ‖v‖ / 2 ≤ dualNorm N v)
    (x : Point D) {k : ℕ} (hk : k < D) (hx : Supported x k) :
    4 * ε ≤ dualNorm N (gradient (scaledObjective a (64 * Real.sqrt ε)) x) ^ 2 := by
  have hx' : Supported (a⁻¹ • x) k := by
    intro j hj
    change a⁻¹ * x j = 0
    rw [hx j hj, mul_zero]
  have hg := gradient_norm_lb hk hx'
  have hs : 0 < (64 : ℝ) * Real.sqrt ε := by positivity
  rw [scaled_grad_value ha]
  have hd := hN ((64 * Real.sqrt ε) • gradient objective (a⁻¹ • x))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs] at hd
  have hn : 2 * Real.sqrt ε ≤ dualNorm N ((64 * Real.sqrt ε) • gradient objective (a⁻¹ • x)) := by
    have h := mul_le_mul_of_nonneg_left hg hs.le
    linarith only [hd, h]
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 2 * Real.sqrt ε) (le_trans (by positivity) hn)).2 hn
  nlinarith only [hsq, Real.sq_sqrt hε.le]

end LongTails.Proofs.BirchResourceChain
