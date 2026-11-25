import LongTails.Proofs.CenteredLogisticDynamics
import LongTails.Algorithms.CenteredLogisticDescent

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.CenteredLogisticSteps

open LongTails.Setups.CenteredLogisticClassification
open LongTails.Setups.ManySampleConvolutionalPerceptron (Space Reply)
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift margin direction)
open LongTails.Algorithms.CenteredLogisticDescent
open CenteredLogisticGeometry CenteredLogisticReadout CenteredLogisticDynamics
open TwoSampleQuadraticPerceptronEmbedding

variable {p : Params}

noncomputable def replies (D : Data p) (θ : Space p.d) : Batch p := fun i => answer D (i, θ)

noncomputable def step (D : Data p) (η : ℝ) (θ : Space p.d) : Space p.d :=
  θ + η • (𝔼 i, Real.sigmoid (-margin .conv p.d (D i) θ) • direction .conv p.d (D i) θ)

lemma margin_scale {d : ℕ} (x : Features d) (θ : Space d) (a c : ℝ) :
    margin .conv d (a • x) (c • θ) = a * c ^ 2 * margin .conv d x θ := by
  simp only [margin, shift_smul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    real_inner_smul_left, real_inner_smul_right]
  ring

lemma direction_scale {d : ℕ} (x : Features d) (θ : Space d) (a c : ℝ) :
    direction .conv d (a • x) (c • θ) = (a * c) • direction .conv d x θ := by
  simp only [direction, shift_smul, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk,
    real_inner_smul_left, real_inner_smul_right, smul_eq_mul, smul_add, smul_smul]
  congr 1
  · congr 1 <;> ring
  · module

lemma scaled_step (D : Data p) (θ : Space p.d) (η : ℝ) {t : ℝ} (ht : 0 < t) :
    step (fun i => t ^ 2 • D i) (η / t ^ 2) (t⁻¹ • θ) = t⁻¹ • step D η θ := by
  have h1 : t ^ 2 * t⁻¹ ^ 2 = 1 := by field_simp
  have h2 : t ^ 2 * t⁻¹ = t := by field_simp
  unfold step
  have hsample (i : Fin p.n) :
      Real.sigmoid (-margin .conv p.d (t ^ 2 • D i) (t⁻¹ • θ)) •
          direction .conv p.d (t ^ 2 • D i) (t⁻¹ • θ) =
        t • (Real.sigmoid (-margin .conv p.d (D i) θ) • direction .conv p.d (D i) θ) := by
    rw [margin_scale, direction_scale, h1, h2, one_mul, smul_comm]
  simp_rw [hsample]
  rw [← Finset.smul_expect, smul_add, smul_smul, smul_smul]
  congr 2
  field_simp

lemma batch_initial (D : Data p) (choose : Batch p → ℝ × ℝ) :
    let θ := initialPoint p.d
    let b := replies D θ
    batchStep choose (θ, none) b = (step D (choose b).2 ((choose b).1 • θ), some (choose b).2) := by
  dsimp only
  unfold batchStep
  dsimp only
  congr 2
  congr 1
  apply Finset.expect_congr rfl
  intro i _
  have hd := direction_scale (D i) (initialPoint p.d) 1 (choose (replies D (initialPoint p.d))).1
  have hm := margin_scale (D i) (initialPoint p.d) 1 (choose (replies D (initialPoint p.d))).1
  simp only [one_smul, one_mul] at hd hm
  simp only [replies, answer, hm, hd]

lemma batch_later (D : Data p) (choose : Batch p → ℝ × ℝ) (θ : Space p.d) (η : ℝ) :
    batchStep choose (θ, some η) (replies D θ) = (step D η θ, some η) := by
  simp [batchStep, replies, answer, step]

variable {D : Data p} (G : Geometry p D)

lemma observed_tuning : tuning (replies D (initialPoint p.d)) = ((Real.sqrt G.R)⁻¹, 8 / G.R) := by
  have energy : (𝔼 i, ‖D i‖ ^ 2) = G.R ^ 2 := by
    simp_rw [row_scale G, norm_smul, Real.norm_eq_abs, abs_of_pos G.scale_pos, mul_pow]
    rw [← Finset.mul_expect, row_energy, mul_one]
  simp only [tuning, replies, answer, initialPoint, direction, one_smul, zero_smul, add_zero]
  rw [energy, Real.sqrt_sq G.scale_pos.le, ite_eq_left G.scale_pos]

lemma mean_parts {ι : Type*} [Fintype ι] {d : ℕ} (f : ι → Space d) :
    (𝔼 i, f i) = ((𝔼 i, (f i).1.1, 𝔼 i, (f i).1.2), 𝔼 i, (f i).2) := by
  apply Prod.ext
  · apply Prod.ext
    · exact map_expect ((LinearMap.fst ℚ≥0 ℝ ℝ).comp
        (LinearMap.fst ℚ≥0 (ℝ × ℝ) (Features d))) f _
    · exact map_expect ((LinearMap.snd ℚ≥0 ℝ ℝ).comp
        (LinearMap.fst ℚ≥0 (ℝ × ℝ) (Features d))) f _
  · exact map_expect (LinearMap.snd ℚ≥0 (ℝ × ℝ) (Features d)) f _

lemma normalized_first :
    step (row G) 8 (initialPoint p.d) = ((1, 0), first G) := by
  unfold step
  rw [mean_parts]
  simp only [initialPoint, margin, inner_zero_right, mul_zero, add_zero, neg_zero,
    Real.sigmoid_zero, direction, one_smul, zero_smul, Prod.smul_mk, smul_eq_mul,
    Finset.expect_const_zero, ← Finset.smul_expect, mean_row, smul_smul, first, Prod.mk_add_mk,
    zero_add]
  norm_num

lemma normalized_second :
    step (row G) 8 ((1, 0), first G) = finalPoint G := by
  have hmean (B : Fin p.n → Features p.d) :
      (𝔼 i, Real.sigmoid (-score G i) * ⟪B i, first G⟫) =
        ⟪𝔼 i, Real.sigmoid (-score G i) • B i, first G⟫ := by
    conv_rhs => rw [real_inner_comm]
    rw [← mean_inner]
    apply Finset.expect_congr rfl
    intro i _
    rw [real_inner_smul_right, real_inner_comm (first G) (B i)]
  have hshift : (𝔼 i, Real.sigmoid (-score G i) • shift (row G i)) = shift (force G) := by
    simp_rw [← shift_smul, mean_shift]
    rfl
  unfold step
  rw [mean_parts]
  simp only [margin, direction, one_mul, zero_mul, add_zero, one_smul, zero_smul, Prod.smul_mk,
    smul_eq_mul, Prod.mk_add_mk, zero_add]
  change ((1 + 8 * (𝔼 i, Real.sigmoid (-score G i) * ⟪row G i, first G⟫),
    8 * (𝔼 i, Real.sigmoid (-score G i) * ⟪shift (row G i), first G⟫)),
    first G + (8 : ℝ) • force G) = _
  rw [hmean, hmean, hshift]
  rfl

lemma physical_two_steps :
    let θ := initialPoint p.d
    let s := batchStep tuning (θ, none) (replies D θ)
    (batchStep tuning s (replies D s.1)).1 = (Real.sqrt G.R)⁻¹ • finalPoint G := by
  dsimp only
  rw [batch_initial D tuning, observed_tuning G]
  dsimp only
  rw [batch_later]
  have ht := Real.sqrt_pos.mpr G.scale_pos
  have hr := Real.sq_sqrt G.scale_pos.le
  have he : D = fun i => (Real.sqrt G.R) ^ 2 • row G i := by
    funext i
    rw [hr, ← row_scale]
  have hη : 8 / G.R = 8 / Real.sqrt G.R ^ 2 := by rw [hr]
  have equiv_step (θ : Space p.d) : step D (8 / G.R) ((Real.sqrt G.R)⁻¹ • θ) =
      (Real.sqrt G.R)⁻¹ • step (row G) 8 θ :=
    (congrArg₂ (fun X η => step X η ((Real.sqrt G.R)⁻¹ • θ)) he hη).trans (scaled_step _ _ 8 ht)
  rw [equiv_step, normalized_first, equiv_step, normalized_second]

end LongTails.Proofs.CenteredLogisticSteps
