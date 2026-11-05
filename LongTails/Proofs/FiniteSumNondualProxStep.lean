import LongTails.Algorithms.FiniteSumNondualProx
import LongTails.Proofs.FiniteSumNondualProxGeometry
import LongTails.Proofs.ComponentEnvelopeCoupling

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.FiniteSumNondualProxStep

open LongTails.Algorithms.FiniteSumNondualProx
open FiniteSumNondualProxGeometry
open RecursiveEnvelopeGeometry (Model)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def normalVector (μ η : ℝ) (c x w v : E) : E :=
  (1 / η) • (x - w) - v - μ • (w - c)

lemma normalVector_identity (μ η : ℝ) (hη : η ≠ 0) (hd : 1 + η * μ ≠ 0)
    (c x w v : E) :
    normalVector μ η c x w v = ((1 + η * μ) / η) •
      ((1 / (1 + η * μ)) • (x - η • v + (η * μ) • c) - w) := by
  unfold normalVector
  simp only [smul_sub, smul_add, smul_smul]
  have h₁ : (1 + η * μ) / η * (1 / (1 + η * μ)) = 1 / η := by field_simp
  rw [h₁]
  have h₂ : 1 / η * η = 1 := by field_simp
  simp only [← mul_assoc, h₁, h₂, one_smul]
  have h₄ : (1 + η * μ) / η = 1 / η + μ := by field_simp
  rw [h₄]
  module

lemma step_mem {C : Set E} (hne : C.Nonempty) (hco : IsCompact C) (hcv : Convex ℝ C)
    (μ η : ℝ) (c x v : E) : step C μ η c x v ∈ C :=
  (OracleTemplate.SaddlePoint.project_spec hne hco hcv _).1

lemma step_normal {C : Set E} (hne : C.Nonempty) (hco : IsCompact C) (hcv : Convex ℝ C)
    {μ η : ℝ} (hμ : 0 ≤ μ) (hη : 0 < η) (c x v : E) :
    Normal C (step C μ η c x v) (normalVector μ η c x (step C μ η c x v) v) := by
  have hd : 0 < 1 + η * μ := by positivity
  intro u hu
  rw [normalVector_identity μ η hη.ne' hd.ne', real_inner_smul_left]
  exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg hd.le hη.le)
    ((OracleTemplate.SaddlePoint.project_spec hne hco hcv _).2 u hu)

lemma residual_identity (μ η : ℝ) (c x w gx gw : E) :
    regularizedGradient (fun _ => gw) μ c w + normalVector μ η c x w gx =
      LongTails.Algorithms.FiniteSumNondualProx.residual η x w gx gw := by
  unfold regularizedGradient normalVector LongTails.Algorithms.FiniteSumNondualProx.residual
  module

lemma regularizer_three_point {C : Set E} (hne : C.Nonempty) (hco : IsCompact C) (hcv : Convex ℝ C)
    {μ η : ℝ} (hμ : 0 ≤ μ) (hη : 0 < η) (c x v u : E) (hu : u ∈ C) :
    let w := step C μ η c x v
    η * (⟪v, w - u⟫ + μ / 2 * ‖w - c‖ ^ 2 - μ / 2 * ‖u - c‖ ^ 2) ≤
      ‖x - u‖ ^ 2 / 2 - (1 + η * μ) / 2 * ‖w - u‖ ^ 2 - ‖w - x‖ ^ 2 / 2 := by
  let w := step C μ η c x v
  have hn := step_normal hne hco hcv hμ hη c x v u hu
  change ⟪normalVector μ η c x w v, u - w⟫ ≤ 0 at hn
  unfold normalVector at hn
  rw [inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left] at hn
  have hi : ⟪x - w, u - w⟫ = (‖x - w‖ ^ 2 + ‖u - w‖ ^ 2 - ‖x - u‖ ^ 2) / 2 := by
    have h := norm_sub_sq_real (x - w) (u - w)
    rw [show (x - w) - (u - w) = x - u by module] at h
    linarith
  have hc := shifted_square c w u
  have hv : ⟪v, u - w⟫ = -⟪v, w - u⟫ := by rw [← inner_neg_right, neg_sub]
  rw [hi, hv, norm_sub_rev x w, norm_sub_rev u w] at hn
  rw [norm_sub_rev u w] at hc
  have hm := mul_le_mul_of_nonneg_left hn hη.le
  have he : η * (1 / η) = 1 := by field_simp
  change η * (⟪v, w - u⟫ + μ / 2 * ‖w - c‖ ^ 2 - μ / 2 * ‖u - c‖ ^ 2) ≤
    ‖x - u‖ ^ 2 / 2 - (1 + η * μ) / 2 * ‖w - u‖ ^ 2 - ‖w - x‖ ^ 2 / 2
  simp only [mul_sub, ← mul_assoc, he, one_mul, mul_zero] at hm
  nlinarith [congrArg (fun q : ℝ => η * μ * q) hc]

lemma stochastic_step_bound {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {L μ η : ℝ} {f : E → ℝ} {g : E → E}
    (hf : Model L f g) (hμ : 0 ≤ μ) (hη : 0 < η) (hηL : η * L ≤ 1 / 2)
    (c x v u : E) (hu : u ∈ C) :
    let w := step C μ η c x v
    ‖w - u‖ ^ 2 + 2 * η * (regularized f μ c w - regularized f μ c u) ≤
      ‖x - u‖ ^ 2 + 2 * η ^ 2 * ‖v - g x‖ ^ 2 - 2 * η * ⟪v - g x, x - u⟫ := by
  let w := step C μ η c x v
  have ht := regularizer_three_point hne hco hcv hμ hη c x v u hu
  change η * (⟪v, w - u⟫ + μ / 2 * ‖w - c‖ ^ 2 - μ / 2 * ‖u - c‖ ^ 2) ≤
    ‖x - u‖ ^ 2 / 2 - (1 + η * μ) / 2 * ‖w - u‖ ^ 2 - ‖w - x‖ ^ 2 / 2 at ht
  have hf₁ := hf.upper x w
  have hf₂ := hf.lower x u
  have hi : ⟪g x, w - x⟫ - ⟪g x, u - x⟫ = ⟪g x, w - u⟫ := by
    rw [← inner_sub_right]; congr 1; module
  have he : ⟪v, w - u⟫ = ⟪g x, w - u⟫ + ⟪v - g x, x - u⟫ +
      ⟪v - g x, w - x⟫ := by
    rw [add_assoc, ← inner_add_right, show x - u + (w - x) = w - u by module]
    rw [← inner_add_left, add_sub_cancel]
  have hc := real_inner_le_norm (-(v - g x)) (w - x)
  rw [inner_neg_left, norm_neg] at hc
  have hy : -2 * η * ⟪v - g x, w - x⟫ ≤
      2 * η ^ 2 * ‖v - g x‖ ^ 2 + ‖w - x‖ ^ 2 / 2 := by
    have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * η by positivity)
    nlinarith [sq_nonneg (2 * η * ‖v - g x‖ - ‖w - x‖)]
  have hs := mul_le_mul_of_nonneg_right hηL (sq_nonneg ‖w - x‖)
  have hm := mul_nonneg (mul_nonneg hη.le hμ) (sq_nonneg ‖w - u‖)
  have hf₃ : f w - f u ≤ ⟪g x, w - u⟫ + L / 2 * ‖w - x‖ ^ 2 := by linarith
  have hf₄ := mul_le_mul_of_nonneg_left hf₃ (show 0 ≤ 2 * η by positivity)
  change ‖w - u‖ ^ 2 + 2 * η * (regularized f μ c w - regularized f μ c u) ≤ _
  unfold regularized
  rw [he] at ht
  nlinarith

lemma exact_step_descent {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {L μ η : ℝ} {f : E → ℝ} {g : E → E}
    (hf : Model L f g) (hμ : 0 ≤ μ) (hη : 0 < η) (hηL : η * L ≤ 1)
    (c x : E) (hx : x ∈ C) :
    let w := step C μ η c x (g x)
    ‖w - x‖ ^ 2 ≤ 2 * η * (regularized f μ c x - regularized f μ c w) := by
  let w := step C μ η c x (g x)
  have ht := regularizer_three_point hne hco hcv hμ hη c x (g x) x hx
  change η * (⟪g x, w - x⟫ + μ / 2 * ‖w - c‖ ^ 2 - μ / 2 * ‖x - c‖ ^ 2) ≤
    ‖x - x‖ ^ 2 / 2 - (1 + η * μ) / 2 * ‖w - x‖ ^ 2 - ‖w - x‖ ^ 2 / 2 at ht
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div, zero_sub] at ht
  have hf' := mul_le_mul_of_nonneg_left (hf.upper x w) hη.le
  have hs := mul_le_mul_of_nonneg_right hηL (sq_nonneg ‖w - x‖)
  have hn := mul_nonneg (mul_nonneg hη.le hμ) (sq_nonneg ‖w - x‖)
  change ‖w - x‖ ^ 2 ≤ 2 * η * (regularized f μ c x - regularized f μ c w)
  unfold regularized
  nlinarith

lemma exact_step_gap {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {L μ η : ℝ} {f : E → ℝ} {g : E → E}
    (hf : Model L f g) (hμ : 0 ≤ μ) (hη : 0 < η) (hηL : η * L ≤ 1)
    (c x u : E) (hu : u ∈ C) :
    let w := step C μ η c x (g x)
    2 * η * (regularized f μ c w - regularized f μ c u) ≤ ‖x - u‖ ^ 2 := by
  let w := step C μ η c x (g x)
  have ht := regularizer_three_point hne hco hcv hμ hη c x (g x) u hu
  have h₁ := hf.upper x w
  have h₂ := hf.lower x u
  have hi : ⟪g x, w - x⟫ - ⟪g x, u - x⟫ = ⟪g x, w - u⟫ := by
    rw [← inner_sub_right]; congr 1; module
  have hf' : f w - f u ≤ ⟪g x, w - u⟫ + L / 2 * ‖w - x‖ ^ 2 := by linarith
  have hh := mul_le_mul_of_nonneg_left hf' (show 0 ≤ 2 * η by positivity)
  have hs := mul_le_mul_of_nonneg_right hηL (sq_nonneg ‖w - x‖)
  have hn := mul_nonneg (mul_nonneg hη.le hμ) (sq_nonneg ‖w - u‖)
  change η * (⟪g x, w - u⟫ + μ / 2 * ‖w - c‖ ^ 2 - μ / 2 * ‖u - c‖ ^ 2) ≤
    ‖x - u‖ ^ 2 / 2 - (1 + η * μ) / 2 * ‖w - u‖ ^ 2 - ‖w - x‖ ^ 2 / 2 at ht
  change 2 * η * (regularized f μ c w - regularized f μ c u) ≤ ‖x - u‖ ^ 2
  unfold regularized
  nlinarith [sq_nonneg ‖w - u‖]

lemma residual_norm {L η : ℝ} {f : E → ℝ} {g : E → E}
    (hf : Model L f g) (hη : 0 < η) (x w : E) :
    ‖LongTails.Algorithms.FiniteSumNondualProx.residual η x w (g x) (g w)‖ ≤
      (L + 1 / η) * ‖w - x‖ := by
  have hh := norm_add_le (g w - g x) ((1 / η) • (x - w))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hη), norm_sub_rev x w] at hh
  have hl := hf.lipschitz w x
  unfold LongTails.Algorithms.FiniteSumNondualProx.residual
  nlinarith

lemma certificate_squared {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (hf : Model L f g) (hμ : 0 ≤ μ) (c x u : E) (hx : x ∈ C)
    (hmin : IsMinOn (regularized f μ c) C u) :
    let w := step C μ (1 / L) c x (g x)
    ‖LongTails.Algorithms.FiniteSumNondualProx.residual (1 / L) x w (g x) (g w)‖ ^ 2 ≤
      8 * L * (regularized f μ c x - regularized f μ c u) := by
  let w := step C μ (1 / L) c x (g x)
  have hL := hf.pos
  have he : (1 / L) * L = 1 := by field_simp
  have hd := exact_step_descent hne hco hcv hf hμ (one_div_pos.mpr hL) he.le c x hx
  have hg := hmin (step_mem hne hco hcv μ (1 / L) c x (g x))
  change regularized f μ c u ≤ regularized f μ c w at hg
  change ‖w - x‖ ^ 2 ≤ 2 * (1 / L) * (regularized f μ c x - regularized f μ c w) at hd
  have hr := residual_norm hf (one_div_pos.mpr hL) x w
  simp only [one_div_one_div] at hr
  have hp : 0 ≤ (L + L) * ‖w - x‖ := by positivity
  have hs := sq_le_sq₀ (norm_nonneg _) hp |>.mpr hr
  change ‖LongTails.Algorithms.FiniteSumNondualProx.residual (1 / L) x w (g x) (g w)‖ ^ 2 ≤ _
  have hdist : L * ‖w - x‖ ^ 2 ≤ 2 * (regularized f μ c x - regularized f μ c u) := by
    have hh := mul_le_mul_of_nonneg_left hd hL.le
    calc
      L * ‖w - x‖ ^ 2 ≤ L * (2 * (1 / L) * (regularized f μ c x - regularized f μ c w)) := hh
      _ = 2 * (regularized f μ c x - regularized f μ c w) := by field_simp
      _ ≤ 2 * (regularized f μ c x - regularized f μ c u) := by linarith
  have hm := mul_le_mul_of_nonneg_left hdist (show 0 ≤ 4 * L by positivity)
  nlinarith

end LongTails.Proofs.FiniteSumNondualProxStep
