import LongTails.Proofs.AffineResidualSaddle

namespace LongTails.Proofs.AffineResidualGap

open scoped RealInnerProductSpace
open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineResidualSaddle
open LongTails.Proofs.AffineResidualSaddle

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [Fintype ι] in
lemma snapshot_residual_bounds [CompleteSpace E] {C : Set E}
    (s : Snapshot ι E) (f : ι → E → ℝ) (field : ι → E → E)
    {L r : ℝ} (hL : 0 ≤ L)
    (hf : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i x, x ∈ C → HasGradientAt (f i) (field i x) x)
    (hlip : ∀ i x y, x ∈ C → y ∈ C → ‖field i x - field i y‖ ≤ L * ‖x - y‖)
    (hanchor : s.anchor ∈ C) (hvalue : ∀ i, s.value i = f i s.anchor)
    (hfield : ∀ i, s.field i = field i s.anchor)
    {x : E} (hx : x ∈ C) (hd : ‖x - s.anchor‖ ≤ r) (i : ι) :
    (0 ≤ f i x - affine s i x ∧ f i x - affine s i x ≤ L * r ^ 2 / 2) ∧
      ‖field i x - s.field i‖ ≤ L * r := by
  have hv := SmoothFiniteMaximumGeometry.affine_residual_bounds (hf i) (hg i)
    (fun x hx y hy => hlip i x y hx hy) hanchor hx
  have hsq : ‖x - s.anchor‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg (x - s.anchor)]
  have hm := mul_le_mul_of_nonneg_left hsq hL
  simp only [affine, hvalue, hfield]
  refine ⟨⟨hv.1, ?_⟩, ?_⟩
  · nlinarith [hv.2]
  · exact (hlip i x s.anchor hx hanchor).trans (mul_le_mul_of_nonneg_left hd hL)

noncomputable def saddleGap (f : ι → E → ℝ) (anchor : E) (μ τ : ℝ)
    (v u : State ι E) : ℝ :=
  (∑ i, u.probability i * f i v.point) - (∑ i, v.probability i * f i u.point) +
    regularizer anchor μ τ v - regularizer anchor μ τ u

noncomputable def linearizedGap (f : ι → E → ℝ) (g : ι → E) (anchor : E) (μ τ D : ℝ)
    (v u : State ι E) : ℝ :=
  -pairing (∑ i, v.probability i • g i) (fun i => D - f i v.point) u v +
    regularizer anchor μ τ v - regularizer anchor μ τ u

lemma linearized_gap_identity (f : ι → E → ℝ) (g : ι → E) (anchor : E) (μ τ D : ℝ)
    (v u : State ι E) (hv : ∑ i, v.probability i = 1) (hu : ∑ i, u.probability i = 1) :
    linearizedGap f g anchor μ τ D v u - saddleGap f anchor μ τ v u =
      ∑ i, v.probability i * (f i u.point - f i v.point - ⟪g i, u.point - v.point⟫) := by
  have hd : (∑ i, D * (u.probability i - v.probability i)) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hu, hv, sub_self, mul_zero]
  unfold linearizedGap saddleGap pairing
  simp only [sum_inner, real_inner_smul_left, sub_mul, mul_sub, Finset.sum_sub_distrib] at hd ⊢
  have he (p : ι → ℝ) : (∑ i, f i v.point * p i) = ∑ i, p i * f i v.point :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [he u.probability, he v.probability]
  linarith

lemma half_regularizer_model (anchor : E) (μ τ : ℝ) (g : E) (b : ι → ℝ)
    (v u : State ι E) :
    -pairing (g + (μ / 2) • (v.point - anchor))
      (fun i => b i + τ / 2 * Real.log (v.probability i)) u v +
        (regularizer anchor μ τ v - regularizer anchor μ τ u) / 2 =
      -pairing g b u v + regularizer anchor μ τ v - regularizer anchor μ τ u +
        potential μ τ u v / 2 := by
  have hr := regularizer_identity anchor μ τ u v
  rw [pairing_add]
  have hh : pairing ((μ / 2) • (v.point - anchor))
      (fun i => τ / 2 * Real.log (v.probability i)) u v =
        pairing (μ • (v.point - anchor)) (fun i => τ * Real.log (v.probability i)) u v / 2 := by
    unfold pairing
    simp only [real_inner_smul_left, mul_assoc, ← Finset.mul_sum]
    ring
  rw [hh]
  linarith

noncomputable def cachedModel (s : Snapshot ι E) (f : ι → E → ℝ) (g : ι → E)
    (μ τ D : ℝ) (v u : State ι E) : ℝ :=
  let a := (∑ i, v.probability i • s.field i) + (μ / 2) • (v.point - s.anchor)
  let d := fun i => -affine s i v.point + τ / 2 * Real.log (v.probability i)
  let meanPrimal := ∑ i, v.probability i • (g i - s.field i)
  let meanDual := fun i => D - (f i v.point - affine s i v.point);
  -pairing (a + meanPrimal) (fun i => d i + meanDual i) u v +
    (regularizer s.anchor μ τ v - regularizer s.anchor μ τ u) / 2

lemma cached_model_identity (s : Snapshot ι E) (f : ι → E → ℝ) (g : ι → E)
    (μ τ D : ℝ) (v u : State ι E) :
    cachedModel s f g μ τ D v u = linearizedGap f g s.anchor μ τ D v u +
      potential μ τ u v / 2 := by
  have hg : (∑ i, v.probability i • s.field i) + (μ / 2) • (v.point - s.anchor) +
      (∑ i, v.probability i • (g i - s.field i)) =
        (∑ i, v.probability i • g i) + (μ / 2) • (v.point - s.anchor) := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    module
  have hb : (fun i => -affine s i v.point + τ / 2 * Real.log (v.probability i) +
      (D - (f i v.point - affine s i v.point))) =
        (fun i => (D - f i v.point) + τ / 2 * Real.log (v.probability i)) := by
    funext i
    ring
  dsimp only [cachedModel]
  rw [hg, hb, half_regularizer_model]
  rfl

lemma cached_model_dominates_gap (s : Snapshot ι E) (f : ι → E → ℝ) (g : ι → E)
    (μ τ D : ℝ) (v u : State ι E) (hv : ∀ i, 0 ≤ v.probability i)
    (hvsum : ∑ i, v.probability i = 1) (husum : ∑ i, u.probability i = 1)
    (hsupport : ∀ i, f i v.point + ⟪g i, u.point - v.point⟫ ≤ f i u.point) :
    saddleGap f s.anchor μ τ v u + potential μ τ u v / 2 ≤ cachedModel s f g μ τ D v u := by
  have hn : 0 ≤ ∑ i, v.probability i *
      (f i u.point - f i v.point - ⟪g i, u.point - v.point⟫) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hv i) (by linarith [hsupport i])
  have hi := linearized_gap_identity f g s.anchor μ τ D v u hvsum husum
  rw [cached_model_identity]
  linarith

lemma cached_model_convex_gap [CompleteSpace E] {C : Set E}
    (s : Snapshot ι E) (f : ι → E → ℝ) (g : ι → E) (μ τ D : ℝ)
    (v u : State ι E) (hv : ∀ i, 0 ≤ v.probability i)
    (hvsum : ∑ i, v.probability i = 1) (husum : ∑ i, u.probability i = 1)
    (hconv : ∀ i, ConvexOn ℝ C (f i)) (hg : ∀ i, HasGradientAt (f i) (g i) v.point)
    (hvmem : v.point ∈ C) (humem : u.point ∈ C) :
    saddleGap f s.anchor μ τ v u + potential μ τ u v / 2 ≤ cachedModel s f g μ τ D v u := by
  apply cached_model_dominates_gap s f g μ τ D v u hv hvsum husum
  intro i
  have h := OracleTemplate.FrankWolfe.convex_support_on (hconv i) hvmem humem (hg i)
  linarith

lemma model_noise_identity (a mean sample : E) (d meanDual sampleDual : ι → ℝ)
    (u v : State ι E) :
    -pairing (a + mean) (fun i => d i + meanDual i) u v =
      -pairing (a + sample) (fun i => d i + sampleDual i) u v +
        pairing (mean - sample) (fun i => meanDual i - sampleDual i) v u := by
  simp only [pairing, inner_add_left, inner_sub_left, inner_sub_right, add_mul, sub_mul,
    mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

lemma step_gap_bound [Nonempty ι] [CompleteSpace E] {C : Set E}
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (s : Snapshot ι E) (f : ι → E → ℝ) (field : ι → E → E)
    (hf : ∀ i, ConvexOn ℝ C (f i))
    (hfield : ∀ i x, x ∈ C → HasGradientAt (f i) (field i x) x)
    {μ τ η : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (hη : 0 < η) (D : ℝ)
    (state : State ι E) (sample : E) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (u : State ι E) (hu : u.point ∈ C) (husum : ∑ i, u.probability i = 1) :
    let v := predictor C s τ μ η state
    let n := correction (OracleTemplate.SaddlePoint.project C) s τ μ η state v sample b
    let mean := ∑ i, v.probability i • (field i v.point - s.field i)
    let meanDual := fun i => D - (f i v.point - affine s i v.point)
    η * (saddleGap f s.anchor μ τ v u + potential μ τ u v / 2) ≤
      potential μ τ u state - (1 + η / 2) * potential μ τ u n - potential μ τ v state +
        η ^ 2 * ‖sample‖ ^ 2 / (2 * ((1 + η / 2) * μ)) +
          η ^ 2 / ((1 + η / 2) * τ) * (∑ i, v.probability i * (b i) ^ 2) +
            η * pairing (mean - sample) (fun i => meanDual i - b i) v u := by
  let v := predictor C s τ μ η state
  have hv := (predictor_mem_min hC hne s τ μ η state).1
  have hg := cached_model_convex_gap s f (fun i => field i v.point) μ τ D v u
    (fun i => (predictor_probability_pos C s τ μ η state i).le)
    (predictor_probability_sum C s τ μ η state) husum hf (fun i => hfield i v.point hv) hv hu
  have hs := step_perturbation_bound hC hne hconv s hμ hτ hη state sample b hb u hu husum
  have hh := mul_le_mul_of_nonneg_left hg hη.le
  dsimp only [cachedModel] at hh
  rw [model_noise_identity (sample := sample) (sampleDual := b)] at hh
  dsimp only at hs ⊢
  dsimp only [v] at hh
  linarith

end LongTails.Proofs.AffineResidualGap
