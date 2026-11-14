import LongTails.Proofs.PointwiseHessianGeometry
import LongTails.Proofs.PLMinimaxProx
import LongTails.Proofs.TikhonovHomotopy

open scoped RealInnerProductSpace

namespace LongTails.Proofs.PointwiseHessianProx

open OracleTemplate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma residual_distance {g : E → E}
    (hm : ∀ x y, 0 ≤ ⟪g x - g y, x - y⟫) {b : ℝ} (hb : 0 ≤ b)
    (c x z : E) (hz : b • g z + z - c = 0) :
    ‖x - z‖ ≤ ‖b • g x + x - c‖ := by
  have he : b • g x + x - c = b • (g x - g z) + (x - z) := by
    calc
      _ = (b • g x + x - c) - (b • g z + z - c) := by rw [hz, sub_zero]
      _ = _ := by module
  have hi : ‖x - z‖ ^ 2 ≤ ⟪b • g x + x - c, x - z⟫ := by
    rw [he, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have := mul_nonneg hb (hm x z)
    linarith
  have hn := real_inner_le_norm (b • g x + x - c) (x - z)
  rcases eq_or_lt_of_le (norm_nonneg (x - z)) with h | h
  · rw [← h]
    exact norm_nonneg _
  · nlinarith

lemma radius_mono {g : E → E}
    (hm : ∀ x y, 0 ≤ ⟪g x - g y, x - y⟫) {b₁ b₂ : ℝ}
    (hb₁ : 0 < b₁) (hbb : b₁ ≤ b₂) (c z₁ z₂ : E)
    (h₁ : b₁ • g z₁ + z₁ - c = 0) (h₂ : b₂ • g z₂ + z₂ - c = 0) :
    ‖z₁ - c‖ ≤ ‖z₂ - c‖ := by
  apply LongTails.Proofs.TikhonovHomotopy.path_mono (F := g) hm (a := 1) hb₁ hbb
    (c := c) (w := c)
  · simpa [LongTails.Proofs.StiffNewtonStage.resid] using h₁
  · simpa [LongTails.Proofs.StiffNewtonStage.resid] using h₂

lemma radius_half {g : E → E}
    (hm : ∀ x y, 0 ≤ ⟪g x - g y, x - y⟫) {b : ℝ} (hb : 0 < b)
    (c z₁ z₂ : E) (h₁ : b • g z₁ + z₁ - c = 0)
    (h₂ : (2 * b) • g z₂ + z₂ - c = 0) : ‖z₂ - c‖ ≤ 2 * ‖z₁ - c‖ := by
  have he : b • g z₂ + z₂ - c = (1 / 2 : ℝ) • (z₂ - c) := by
    have hh := congrArg (fun y : E => (1 / 2 : ℝ) • y) h₂
    simp only [smul_add, smul_sub, smul_smul, smul_zero] at hh
    have heq : (1 / 2 : ℝ) * (2 * b) = b := by ring
    rw [heq] at hh
    apply sub_eq_zero.mp
    calc
      (b • g z₂ + z₂ - c) - (1 / 2 : ℝ) • (z₂ - c) =
        b • g z₂ + (1 / 2 : ℝ) • z₂ - (1 / 2 : ℝ) • c := by module
      _ = 0 := hh
  have hd := residual_distance hm hb.le c z₂ z₁ h₁
  rw [he, norm_smul] at hd
  norm_num at hd
  have hn := norm_add_le (z₂ - z₁) (z₁ - c)
  have hsum : z₂ - z₁ + (z₁ - c) = z₂ - c := by abel
  rw [hsum] at hn
  nlinarith

lemma root_radius {g : E → E}
    (hm : ∀ x y, 0 ≤ ⟪g x - g y, x - y⟫) {b : ℝ} (hb : 0 ≤ b)
    (c z s : E) (hs : g s = 0) (hz : b • g z + z - c = 0) :
    ‖z - c‖ ^ 2 + ‖z - s‖ ^ 2 ≤ ‖c - s‖ ^ 2 := by
  have hm' := hm z s
  rw [hs, sub_zero] at hm'
  have he : c - z = b • g z := by
    have hh := sub_eq_zero.mp hz
    rw [← hh]
    abel
  have hi : 0 ≤ ⟪c - z, z - s⟫ := by
    rw [he, real_inner_smul_left]
    exact mul_nonneg hb hm'
  have hsum : c - z + (z - s) = c - s := by abel
  have hn := norm_add_sq_real (c - z) (z - s)
  rw [hsum, norm_sub_rev c z] at hn
  linarith

omit [InnerProductSpace ℝ E] in
lemma adequate_guard (c x z d : E) {r q : ℝ} (hr : 0 ≤ r)
    (hx : ‖x - z‖ ≤ q) (hz : ‖z - c‖ ≤ r / 2)
    (hd : ‖d‖ ≤ q) (hq : q ≤ r / 8) : ‖x + d - c‖ ≤ 2 * r := by
  have h1 := norm_add_le (x - z) (z - c)
  have h2 := norm_add_le ((x - z) + (z - c)) d
  have he : (x - z) + (z - c) + d = x + d - c := by abel
  rw [he] at h2
  linarith

lemma relative_radius {g : E → E}
    (hm : ∀ x y, 0 ≤ ⟪g x - g y, x - y⟫) {b : ℝ} (hb : 0 ≤ b)
    (c x z : E) (hz : b • g z + z - c = 0)
    (hx : ‖b • g x + x - c‖ ≤ ‖x - c‖ / 2) : ‖z - c‖ ≤ 3 * ‖x - c‖ / 2 := by
  have hd := residual_distance hm hb c x z hz
  have hn := norm_add_le (z - x) (x - c)
  have he : z - x + (x - c) = z - c := by abel
  rw [he, norm_sub_rev z x] at hn
  linarith

section Convex

variable [CompleteSpace E] [FiniteDimensional ℝ E]

lemma proximal_exists {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {b : ℝ} (hb : 0 < b) (c : E) :
    ∃ z, b • gradient f z + z - c = 0 := by
  have hL : 0 < 1 / (2 * b) := by positivity
  have hg (x : E) : HasGradientAt f (gradient f x) x :=
    (hf.differentiable (by norm_num) x).hasGradientAt
  have hw : WeaklyConvexHeavyTailed.WeakSubgradientOn Set.univ (1 / (2 * b)) f (gradient f) := by
    intro x _ y _
    have hh := Gradient.convex_support hc hg x y
    have hp : 0 ≤ (1 / (2 * b)) / 2 * ‖y - x‖ ^ 2 := by positivity
    linarith
  let z := PLMinimax.weakProx f (1 / (2 * b)) c
  have hs := PLMinimax.weakProx_stationary hL hg hw c
  change gradient f z + (2 * (1 / (2 * b))) • (z - c) = 0 at hs
  have hh := congrArg (fun y : E => b • y) hs
  simp only [smul_add, smul_smul, smul_zero] at hh
  have he : b * (2 * (1 / (2 * b))) = 1 := by field_simp
  rw [he, one_smul] at hh
  exact ⟨z, by simpa only [add_sub_assoc] using hh⟩

omit [FiniteDimensional ℝ E] in
lemma gradient_gap {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) (x s : E) :
    f x - f s ≤ ‖gradient f x‖ * ‖x - s‖ := by
  have hg (y : E) : HasGradientAt f (gradient f y) y :=
    (hf.differentiable (by norm_num) y).hasGradientAt
  have hh := Gradient.convex_support hc hg x s
  have hi := real_inner_le_norm (gradient f x) (x - s)
  have he : s - x = -(x - s) := by abel
  rw [he, inner_neg_right] at hh
  linarith

end Convex

end LongTails.Proofs.PointwiseHessianProx
