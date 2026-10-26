import LongTails.Proofs.ComponentEnvelopeCoupling
open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators
namespace OracleTemplate.ComponentEnvelope
open LongTails.Proofs.RecursiveEnvelopeGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma model_convex {f : E → ℝ} {g : E → E} {μ : ℝ} (hm : Model μ f g) :
    ConvexOn ℝ univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  have hx := mul_le_mul_of_nonneg_left (hm.lower z x) ha
  have hy := mul_le_mul_of_nonneg_left (hm.lower z y) hb
  have he : a • (x - z) + b • (y - z) = 0 := by
    rw [smul_sub, smul_sub]
    calc
      _ = z - (a + b) • z := by dsimp [z]; module
      _ = 0 := by rw [hab]; simp
  have hi := congrArg (fun v => ⟪g z, v⟫) he
  simp only [inner_add_right, inner_smul_right, inner_zero_right] at hi
  change f z ≤ a * f x + b * f y
  have hsum : (a + b) * f z = f z := by rw [hab, one_mul]
  nlinarith only [hx, hy, hi, hsum]

lemma model_gradient_gap {f : E → ℝ} {g : E → E} {μ : ℝ} (hm : Model μ f g)
    {u : E} (hgu : g u = 0) (x : E) :
    ‖g x‖ ^ 2 ≤ 2 * μ * (f x - f u) := by
  simpa [hgu] using hm.bregman x u

lemma model_interpolated_step {f : E → ℝ} {g : E → E} {μ : ℝ} (hm : Model μ f g)
    {u : E} (hgu : g u = 0) (x : E) :
    ‖x - (1 / (2 * μ)) • g x - u‖ ^ 2 ≤
      ‖x - u‖ ^ 2 - (f x - f u) / (2 * μ) := by
  have hs := model_gradient_gap hm hgu x
  have hc := hm.lower x u
  have he : x - (1 / (2 * μ)) • g x - u =
      (x - u) - (1 / (2 * μ)) • g x := by module
  rw [he, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_right]
  have hi : ⟪x - u, g x⟫ = -⟪g x, u - x⟫ := by
    rw [real_inner_comm, ← inner_neg_right, neg_sub]
  rw [hi]
  have hμ := hm.pos
  apply (mul_le_mul_iff_right₀ (show 0 < 4 * μ ^ 2 by positivity)).mp
  field_simp
  nlinarith

lemma projection_squared_distance {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) (x u : E) (hu : u ∈ C) :
    ‖SaddlePoint.project C x - u‖ ^ 2 ≤ ‖x - u‖ ^ 2 := by
  have hh := SaddlePoint.project_inequality hne hco hcv 0 x 0 u hu
  simp only [zero_smul, sub_zero, mul_zero, zero_mul] at hh
  nlinarith [sq_nonneg ‖x - SaddlePoint.project C x‖]

lemma projected_warmup_step {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {f : E → ℝ} {g : E → E} {μ R ζ : ℝ}
    (hm : Model μ f g) (hR : 0 ≤ R) (x u v : E) (hu : u ∈ C) (hgu : g u = 0)
    (hrad : ∀ a ∈ C, ‖a - u‖ ≤ 2 * R) (herr : ‖v - g x‖ ≤ ζ) :
    f x - f u ≤ 2 * μ * (‖x - u‖ ^ 2 -
      ‖SaddlePoint.project C (x - (1 / (2 * μ)) • v) - u‖ ^ 2) + 4 * R * ζ := by
  let Y := fun a => SaddlePoint.project C (x - (1 / (2 * μ)) • a)
  have hym : ∀ a, Y a ∈ C := fun a => (SaddlePoint.project_spec hne hco hcv _).1
  have hμ := hm.pos
  have hstep := (projection_squared_distance hne hco hcv (x - (1 / (2 * μ)) • g x) u hu).trans
    (model_interpolated_step hm hgu x)
  have hdist := (projected_gradient_perturbation hne hco hcv
    (by positivity : 0 ≤ 1 / (2 * μ)) x v (g x)).trans
      (mul_le_mul_of_nonneg_left herr (by positivity : 0 ≤ 1 / (2 * μ)))
  have hsq := squared_distance_perturbation (hrad (Y v) (hym v)) (hrad (Y (g x)) (hym (g x)))
  have hp := hsq.trans (mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ 4 * R))
  have hscaled := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * μ by positivity)
  have hid : 2 * μ * (4 * R * (1 / (2 * μ) * ζ)) = 4 * R * ζ := by field_simp
  rw [hid] at hscaled
  have hstepscaled := mul_le_mul_of_nonneg_left hstep (show 0 ≤ 2 * μ by positivity)
  have hdiv : 2 * μ * ((f x - f u) / (2 * μ)) = f x - f u := by field_simp
  change ‖Y (g x) - u‖ ^ 2 ≤ ‖x - u‖ ^ 2 - (f x - f u) / (2 * μ) at hstep
  change f x - f u ≤ 2 * μ * (‖x - u‖ ^ 2 - ‖Y v - u‖ ^ 2) + 4 * R * ζ
  change 2 * μ * ‖Y (g x) - u‖ ^ 2 ≤ 2 * μ * (‖x - u‖ ^ 2 - (f x - f u) / (2 * μ)) at hstepscaled
  rw [mul_sub, hdiv] at hstepscaled
  nlinarith
lemma model_displacement_gap {f : E → ℝ} {g : E → E} {μ : ℝ} (hm : Model μ f g)
    {u : E} (hgu : g u = 0) (w d : E) :
    f (w + d) - f u ≤ 2 * (f w - f u) + μ * ‖d‖ ^ 2 := by
  have hs := model_gradient_gap hm hgu w
  have hu := hm.upper w (w + d)
  simp only [add_sub_cancel_left] at hu
  have hi := real_inner_le_norm (g w) d
  have hy := sq_nonneg (‖g w‖ - μ * ‖d‖)
  have hμ := hm.pos
  nlinarith

lemma model_query_gap {f : E → ℝ} {g : E → E} {μ : ℝ} (hm : Model μ f g)
    {u : E} (hgu : g u = 0) (w y z : E) (τ : ℝ) :
    f (τ • z + (1 / 2 : ℝ) • w + (1 / 2 - τ) • y) - f u ≤
      (f w - f u) + (f y - f u) + μ * τ ^ 2 * ‖z - y‖ ^ 2 := by
  have h := model_displacement_gap hm hgu ((1 / 2 : ℝ) • w + (1 / 2 : ℝ) • y) (τ • (z - y))
  have hmid := (model_convex hm).2 (mem_univ w) (mem_univ y)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have he : (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • y + τ • (z - y) =
      τ • z + (1 / 2 : ℝ) • w + (1 / 2 - τ) • y := by module
  rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
  simp only [smul_eq_mul] at hmid
  nlinarith


end OracleTemplate.ComponentEnvelope
