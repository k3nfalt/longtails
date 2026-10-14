import LongTails.Proofs.WeaklyConvexMoreau
import LongTails.Proofs.HeavyTailedClipping
import LongTails.Algorithms.ClippedProjectedSubgradient
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.WeaklyConvexHeavyTailed

open LongTails.Setups.WeaklyConvexHeavyTailed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma projection_nonexpansive_point {D : Set E} {proj : E → E}
    (hproj : ∀ y, ∀ u ∈ D, ⟪y - proj y, u - proj y⟫ ≤ 0) {u : E} (hu : u ∈ D) (y : E) :
    ‖u - proj y‖ ≤ ‖u - y‖ := by
  have h := hproj y u hu
  have he : u - y = (u - proj y) - (y - proj y) := by abel
  have hex := norm_sub_sq_real (u - proj y) (y - proj y)
  rw [← he, real_inner_comm] at hex
  have hsq : ‖u - proj y‖ ^ 2 ≤ ‖u - y‖ ^ 2 := by nlinarith [sq_nonneg ‖y - proj y‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

lemma projection_fixed {D : Set E} {proj : E → E}
    (hproj : ∀ y, ∀ u ∈ D, ⟪y - proj y, u - proj y⟫ ≤ 0) {x : E} (hx : x ∈ D) : proj x = x := by
  have h := hproj x x hx
  rw [real_inner_self_eq_norm_sq] at h
  have : ‖x - proj x‖ = 0 := by nlinarith [sq_nonneg ‖x - proj x‖, norm_nonneg (x - proj x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp this)).symm

lemma projection_nonexpansive {D : Set E} {proj : E → E}
    (hproj : ∀ y, ∀ u ∈ D, ⟪y - proj y, u - proj y⟫ ≤ 0) (hprojD : ∀ y, proj y ∈ D) (y z : E) :
    ‖proj y - proj z‖ ≤ ‖y - z‖ := by
  have h1 := hproj y (proj z) (hprojD z)
  have h2 := hproj z (proj y) (hprojD y)
  have he : y - z = (proj y - proj z) + ((y - proj y) - (z - proj z)) := by abel
  have hsq : ‖proj y - proj z‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by
    rw [he, norm_add_sq_real]
    have hi : 0 ≤ ⟪proj y - proj z, (y - proj y) - (z - proj z)⟫ := by
      rw [inner_sub_right]
      have e1 : ⟪proj y - proj z, y - proj y⟫ = -⟪y - proj y, proj z - proj y⟫ := by
        rw [real_inner_comm, ← inner_neg_right]; congr 1; abel
      have e2 : ⟪proj y - proj z, z - proj z⟫ = ⟪z - proj z, proj y - proj z⟫ := real_inner_comm _ _
      rw [e1, e2]
      linarith
    nlinarith [sq_nonneg ‖(y - proj y) - (z - proj z)‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

noncomputable def envelope (f : E → ℝ) (ρ : ℝ) (prox : E → E) (y : E) : ℝ :=
  proxObj f ρ y (prox y)

omit [InnerProductSpace ℝ E] in
lemma envelope_le_f {D : Set E} {f : E → ℝ} {ρ : ℝ} {prox : E → E}
    (hprox : IsProx f D ρ prox) {x : E} (hx : x ∈ D) : envelope f ρ prox x ≤ f x := by
  have := (hprox x).2 hx
  simpa [envelope, proxObj] using this

omit [InnerProductSpace ℝ E] in
lemma envelope_ge {D : Set E} {f : E → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) {prox : E → E}
    (hprox : IsProx f D ρ prox) {lower : ℝ} (hlow : ∀ y ∈ D, lower ≤ f y) (x : E) :
    lower ≤ envelope f ρ prox x := by
  have h1 := hlow _ (hprox x).1
  have h2 : 0 ≤ ρ * ‖prox x - x‖ ^ 2 := by positivity
  unfold envelope proxObj
  linarith

lemma prox_lipschitzWith {D : Set E} (hD : Convex ℝ D) {ρ : ℝ} {f : E → ℝ} {v : E → E}
    (hv : WeakSubgradientOn D ρ f v) (hρ : 0 < ρ) {prox : E → E}
    (hprox : IsProx f D ρ prox) : LipschitzWith 2 prox := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm]
  simpa using prox_lipschitz hD hv hρ (hprox x).1 (hprox x).2 (hprox y).1 (hprox y).2

lemma continuous_envelope {D : Set E} (hD : Convex ℝ D) {ρ G : ℝ} {f : E → ℝ} {v : E → E}
    (hv : WeakSubgradientOn D ρ f v) (hG : ∀ x ∈ D, ‖v x‖ ≤ G) (hρ : 0 < ρ) (hG0 : 0 ≤ G)
    {prox : E → E} (hprox : IsProx f D ρ prox) : Continuous (envelope f ρ prox) := by
  have hpc : Continuous prox := (prox_lipschitzWith hD hv hρ hprox).continuous
  have hfp : Continuous (fun y => f (prox y)) :=
    (continuousOn_of_weak hv hG hρ.le hG0).comp_continuous hpc (fun y => (hprox y).1)
  unfold envelope proxObj
  exact hfp.add (((hpc.sub continuous_id).norm.pow 2).const_smul ρ)

lemma one_step_det {D : Set E} {ρ : ℝ} {f : E → ℝ}
    (hρ : 0 < ρ) {prox : E → E} (hprox : IsProx f D ρ prox)
    {proj : E → E} (hproj : ∀ y, ∀ u ∈ D, ⟪y - proj y, u - proj y⟫ ≤ 0) (x : E) (γ : ℝ) (g : E) :
    envelope f ρ prox (proj (x - γ • g)) ≤
      envelope f ρ prox x + 2 * ρ * γ * ⟪g, prox x - x⟫ + ρ * γ ^ 2 * ‖g‖ ^ 2 := by
  unfold envelope
  exact envelope_step hρ.le (hprox x).1 (hprox _).2 γ g
    (projection_nonexpansive_point hproj (hprox x).1 _)

section Expectation

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E]

lemma one_step_expectation {D : Set E} (hD : Convex ℝ D) {ρ G σ α τ γ : ℝ} {f : E → ℝ}
    {v : E → E} (hv : WeakSubgradientOn D ρ f v) (hG : ∀ x ∈ D, ‖v x‖ ≤ G) (hρ : 0 < ρ)
    (hα : 1 ≤ α) (hα2 : α ≤ 2) (hτ : 2 * G ≤ τ) (hτ0 : 0 < τ) (hγ : 0 ≤ γ)
    {prox : E → E} (hprox : IsProx f D ρ prox)
    {proj : E → E} (hproj : ∀ y, ∀ u ∈ D, ⟪y - proj y, u - proj y⟫ ≤ 0)
    {ν : Measure Ω} [IsProbabilityMeasure ν] {g : E → Ω → E} (hgm : Measurable (Function.uncurry g))
    {x : E} (hx : x ∈ D) (hgi : Integrable (g x) ν) (hmean : ∫ ω, g x ω ∂ν = v x)
    (hmi : Integrable (fun ω => ‖g x ω - v x‖ ^ α) ν)
    (hm : (∫ ω, ‖g x ω - v x‖ ^ α ∂ν) ≤ σ ^ α)
    (hint : Integrable (fun ω => envelope f ρ prox (proj (x - γ • clip τ (g x ω)))) ν) :
    (∫ ω, envelope f ρ prox (proj (x - γ • clip τ (g x ω))) ∂ν) ≤
      envelope f ρ prox x - ρ ^ 2 * γ * ‖prox x - x‖ ^ 2 +
        γ * (σ ^ α / (τ / 2) ^ (α - 1)) ^ 2 +
        2 * ρ * γ ^ 2 * (G ^ 2 + (2 * τ) ^ (2 - α) * σ ^ α) := by
  have hgx : Measurable (g x) := hgm.comp (measurable_const.prodMk measurable_id)
  have hvG : ‖v x‖ ≤ G := hG x hx
  have hvτ2 : ‖v x‖ ≤ τ / 2 := by linarith
  have hvτ : ‖v x‖ ≤ τ := by linarith [norm_nonneg (v x)]
  have hci : Integrable (fun ω => clip τ (g x ω)) ν :=
    Integrable.of_bound ((measurable_clip τ).comp hgx).aestronglyMeasurable τ
      (Filter.Eventually.of_forall (fun ω => norm_clip_le hτ0.le _))
  have hbias := clipped_bias_bound (P := ν) hgx hgi hmean hτ0 hα hvτ2 hmi hm
  have hsec := clipped_second_moment_bound (P := ν) hgx hτ0.le (by linarith) hα2 hvτ hmi hm
  have hsqi : Integrable (fun ω => ‖clip τ (g x ω)‖ ^ 2) ν := by
    refine Integrable.of_bound (((measurable_clip τ).comp hgx).norm.pow_const 2).aestronglyMeasurable
      (τ ^ 2) (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_clip_le hτ0.le _) 2
  have hsq2i : Integrable (fun ω => ‖clip τ (g x ω) - v x‖ ^ 2) ν := by
    refine Integrable.of_bound ((((measurable_clip τ).comp hgx).sub_const _).norm.pow_const 2).aestronglyMeasurable
      ((τ + ‖v x‖) ^ 2) (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2
    linarith [norm_clip_le hτ0.le (g x ω)]
  set w := prox x - x with hw
  have hpt : ∀ ω, envelope f ρ prox (proj (x - γ • clip τ (g x ω))) ≤
      envelope f ρ prox x + 2 * ρ * γ * ⟪w, clip τ (g x ω)⟫ +
        ρ * γ ^ 2 * ‖clip τ (g x ω)‖ ^ 2 := by
    intro ω
    have := one_step_det hρ hprox hproj x γ (clip τ (g x ω))
    rwa [real_inner_comm] at this
  have hA : Integrable (fun ω => envelope f ρ prox x + 2 * ρ * γ * ⟪w, clip τ (g x ω)⟫) ν := by
    have := (integrable_const (μ := ν) (envelope f ρ prox x)).add
      ((hci.const_inner w).const_mul (2 * ρ * γ))
    exact this
  have hB : Integrable (fun ω => ρ * γ ^ 2 * ‖clip τ (g x ω)‖ ^ 2) ν := hsqi.const_mul _
  have hrhs : Integrable (fun ω => envelope f ρ prox x + 2 * ρ * γ * ⟪w, clip τ (g x ω)⟫ +
      ρ * γ ^ 2 * ‖clip τ (g x ω)‖ ^ 2) ν := hA.add hB
  have hI := integral_mono hint hrhs hpt
  have hA' : Integrable (fun ω => 2 * ρ * γ * ⟪w, clip τ (g x ω)⟫) ν :=
    (hci.const_inner w).const_mul (2 * ρ * γ)
  have hsplit_int : (∫ ω, envelope f ρ prox x + 2 * ρ * γ * ⟪w, clip τ (g x ω)⟫ +
      ρ * γ ^ 2 * ‖clip τ (g x ω)‖ ^ 2 ∂ν) =
      envelope f ρ prox x + 2 * ρ * γ * ⟪w, ∫ ω, clip τ (g x ω) ∂ν⟫ +
        ρ * γ ^ 2 * ∫ ω, ‖clip τ (g x ω)‖ ^ 2 ∂ν := by
    rw [integral_add hA hB, integral_add (integrable_const _) hA', integral_const,
      integral_const_mul, integral_const_mul, integral_inner hci w]
    simp only [probReal_univ, one_smul]
  rw [hsplit_int] at hI
  have hvin : ⟪w, v x⟫ ≤ -ρ * ‖w‖ ^ 2 := by
    have := inner_weak_prox hD hv hρ hx (hprox x).1 (hprox x).2
    rwa [real_inner_comm] at this
  have hsplit : ⟪w, ∫ ω, clip τ (g x ω) ∂ν⟫ = ⟪w, v x⟫ + ⟪w, (∫ ω, clip τ (g x ω) ∂ν) - v x⟫ := by
    rw [inner_sub_right]; ring
  have hcs : ⟪w, (∫ ω, clip τ (g x ω) ∂ν) - v x⟫ ≤ ‖w‖ * (σ ^ α / (τ / 2) ^ (α - 1)) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hbias (norm_nonneg _))
  have hsq_split : (∫ ω, ‖clip τ (g x ω)‖ ^ 2 ∂ν) ≤ 2 * G ^ 2 + 2 * ((2 * τ) ^ (2 - α) * σ ^ α) := by
    have hpt2 : ∀ ω, ‖clip τ (g x ω)‖ ^ 2 ≤ 2 * ‖v x‖ ^ 2 + 2 * ‖clip τ (g x ω) - v x‖ ^ 2 := by
      intro ω
      have := norm_add_le (clip τ (g x ω) - v x) (v x)
      rw [sub_add_cancel] at this
      have hsq := pow_le_pow_left₀ (norm_nonneg _) this 2
      nlinarith [hsq, sq_nonneg (‖clip τ (g x ω) - v x‖ - ‖v x‖)]
    have hC : Integrable (fun ω => 2 * ‖v x‖ ^ 2 + 2 * ‖clip τ (g x ω) - v x‖ ^ 2) ν := by
      have := (integrable_const (μ := ν) (2 * ‖v x‖ ^ 2)).add (hsq2i.const_mul 2)
      exact this
    have := integral_mono hsqi hC hpt2
    rw [integral_add (integrable_const _) (hsq2i.const_mul 2), integral_const, integral_const_mul] at this
    simp only [probReal_univ, one_smul] at this
    have hG2 : ‖v x‖ ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvG 2
    linarith [hsec]
  have hyoung : 2 * ρ * γ * (‖w‖ * (σ ^ α / (τ / 2) ^ (α - 1))) ≤
      ρ ^ 2 * γ * ‖w‖ ^ 2 + γ * (σ ^ α / (τ / 2) ^ (α - 1)) ^ 2 := by
    have := mul_nonneg hγ (sq_nonneg (ρ * ‖w‖ - σ ^ α / (τ / 2) ^ (α - 1)))
    nlinarith [this]
  have hργ : 0 ≤ 2 * ρ * γ := by positivity
  have hργ2 : 0 ≤ ρ * γ ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hcs hργ
  have h2 := mul_le_mul_of_nonneg_left hvin hργ
  have h3 := mul_le_mul_of_nonneg_left hsq_split hργ2
  rw [hsplit] at hI
  linarith [hI, h1, h2, h3, hyoung]

end Expectation

end OracleTemplate.WeaklyConvexHeavyTailed
