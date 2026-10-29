import LongTails.Proofs.ComponentEnvelopeCoupling
import LongTails.Proofs.StochasticEnvelopeGeometry
import LongTails.Algorithms.NondualSelector
import Mathlib.Analysis.Convex.Integral

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.NondualProjection

open OracleTemplate.SaddlePoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def value (K : Set E) (x : E) : ℝ :=
  ‖project K x‖ ^ 2 / 2 - ⟪x, project K x⟫

lemma value_minimum {K : Set E} (hne : K.Nonempty) (hco : IsCompact K)
    (hcv : Convex ℝ K) (x : E) {u : E} (hu : u ∈ K) :
    value K x ≤ ‖u‖ ^ 2 / 2 - ⟪x, u⟫ := by
  have hp := (project_spec hne hco hcv x).2 u hu
  simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq] at hp
  have hs := norm_sub_sq_real u (project K x)
  have hi : ⟪u, project K x⟫ = ⟪project K x, u⟫ := real_inner_comm _ _
  rw [hi] at hs
  dsimp [value]
  nlinarith [sq_nonneg ‖u - project K x‖]

lemma value_upper {K : Set E} (hne : K.Nonempty) (hco : IsCompact K)
    (hcv : Convex ℝ K) (x y : E) :
    value K y ≤ value K x - ⟪project K x, y - x⟫ := by
  have h := value_minimum hne hco hcv y (project_spec hne hco hcv x).1
  dsimp [value] at h ⊢
  have hy : ⟪project K x, y⟫ = ⟪y, project K x⟫ := real_inner_comm _ _
  have hx : ⟪project K x, x⟫ = ⟪x, project K x⟫ := real_inner_comm _ _
  rw [inner_sub_right, hy, hx]
  linarith

lemma value_lower {K : Set E} (hne : K.Nonempty) (hco : IsCompact K)
    (hcv : Convex ℝ K) (x y : E) :
    value K x - ⟪project K x, y - x⟫ - ‖y - x‖ ^ 2 ≤ value K y := by
  have h := value_upper hne hco hcv y x
  have hp := OracleTemplate.ComponentEnvelope.projection_nonexpansive hne hco hcv y x
  have hi := real_inner_le_norm (project K y - project K x) (y - x)
  have hm := mul_le_mul_of_nonneg_right hp (norm_nonneg (y - x))
  have he : ⟪project K y, x - y⟫ = -⟪project K y, y - x⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [he] at h
  rw [inner_sub_left] at hi
  nlinarith

lemma negative_value_model {K : Set E} (hne : K.Nonempty) (hco : IsCompact K)
    (hcv : Convex ℝ K) :
    RecursiveEnvelopeGeometry.Model 2 (fun x => -value K x) (project K) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro x y
    linarith [value_upper hne hco hcv x y]
  · intro x y
    norm_num
    linarith [value_lower hne hco hcv x y]

lemma value_hasGradientAt [CompleteSpace E] {K : Set E} (hne : K.Nonempty)
    (hco : IsCompact K) (hcv : Convex ℝ K) (x : E) :
    HasGradientAt (value K) (-project K x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (StochasticEnvelopeGeometry.model_hasGradientAt
    (negative_value_model hne hco hcv) x).hasFDerivAt.neg
  change HasFDerivAt (fun y => - -value K y)
    (-(InnerProductSpace.toDual ℝ E) (project K x)) x at h
  simpa only [neg_neg, map_neg] using h

lemma project_lipschitz {K : Set E} (hne : K.Nonempty) (hco : IsCompact K)
    (hcv : Convex ℝ K) : LipschitzWith 1 (project K) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [dist_eq_norm] using
    OracleTemplate.ComponentEnvelope.projection_nonexpansive hne hco hcv x y

lemma value_continuous {K : Set E} (hne : K.Nonempty) (hco : IsCompact K)
    (hcv : Convex ℝ K) : Continuous (value K) := by
  have hp := (project_lipschitz hne hco hcv).continuous
  unfold value
  fun_prop

lemma value_mono {K L : Set E} (hne : K.Nonempty) (hco : IsCompact K)
    (hcv : Convex ℝ K) (hneL : L.Nonempty) (hcoL : IsCompact L)
    (hcvL : Convex ℝ L) (hLK : L ⊆ K) (x : E) : value K x ≤ value L x := by
  exact value_minimum hne hco hcv x (hLK (project_spec hneL hcoL hcvL x).1)

lemma value_bounds {K : Set E} (hne : K.Nonempty) (hco : IsCompact K)
    (hcv : Convex ℝ K) {R B : ℝ} (x : E)
    (hnorm : ∀ u ∈ K, ‖u‖ ≤ R) (hinner : ∀ u ∈ K, |⟪x, u⟫| ≤ B) :
    -B ≤ value K x ∧ value K x ≤ R ^ 2 / 2 + B := by
  have hp := (project_spec hne hco hcv x).1
  have hi := abs_le.mp (hinner _ hp)
  have hn := pow_le_pow_left₀ (norm_nonneg _) (hnorm _ hp) 2
  dsimp [value]
  constructor <;> nlinarith [sq_nonneg ‖project K x‖]

end LongTails.Proofs.NondualProjection

namespace LongTails.Proofs.NondualProjection

open MeasureTheory Metric OracleTemplate.ZerothOrder OracleTemplate.SaddlePoint
open LongTails.Algorithms.NondualSelector

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0 : E) 1
local notation "Q" => (sphereLaw E : Measure S)
local notation "P" => (radialLaw d (NeZero.pos d) : Measure ℝ)

lemma center_integrable {K : Set E} (hne : K.Nonempty) (hco : IsCompact K)
    (hcv : Convex ℝ K) (r : ℝ) :
    Integrable (fun v : ℝ × S => project K (r • ballOffset v)) ((P).prod Q) := by
  simpa only [zero_add] using
    ball_offset_continuous_integrable (project_lipschitz hne hco hcv).continuous (0 : E) r

lemma center_mem {K : Set E} (hne : K.Nonempty) (hco : IsCompact K)
    (hcv : Convex ℝ K) (r : ℝ) : center K r ∈ K := by
  exact hcv.integral_mem hco.isClosed
    (Filter.Eventually.of_forall fun _ => (project_spec hne hco hcv _).1)
    (center_integrable hne hco hcv r)

lemma center_boundary {K : Set E} (hne : K.Nonempty) (hco : IsCompact K)
    (hcv : Convex ℝ K) {r : ℝ} (hr : r ≠ 0) :
    center K r = -(∫ u : S, ((d : ℝ) / r * value K (r • (u : E))) • (u : E) ∂Q) := by
  have h := ball_boundary_gradient (value_continuous hne hco hcv)
    (project_lipschitz hne hco hcv).continuous.neg
    (value_hasGradientAt hne hco hcv) (0 : E) hr
  simp only [zero_add, Pi.neg_apply, integral_neg] at h
  change -center K r = _ at h
  exact neg_eq_iff_eq_neg.mp h

lemma center_difference {K L : Set E} (hne : K.Nonempty) (hco : IsCompact K)
    (hcv : Convex ℝ K) (hneL : L.Nonempty) (hcoL : IsCompact L)
    (hcvL : Convex ℝ L) {r : ℝ} (hr : r ≠ 0) :
    center L r - center K r =
      -(∫ u : S, ((d : ℝ) / r * (value L (r • (u : E)) - value K (r • (u : E)))) •
        (u : E) ∂Q) := by
  have hi (X : Set E) (hX : Continuous (value X)) :
      Integrable (fun u : S => ((d : ℝ) / r * value X (r • (u : E))) • (u : E)) Q :=
    sphere_integrable_continuous_map (f := fun u : E =>
      ((d : ℝ) / r * value X (r • u)) • u) (by fun_prop)
  rw [center_boundary hneL hcoL hcvL hr, center_boundary hne hco hcv hr]
  simp_rw [mul_sub, sub_smul]
  rw [integral_sub (hi L (value_continuous hneL hcoL hcvL))
    (hi K (value_continuous hne hco hcv))]
  abel

end LongTails.Proofs.NondualProjection
