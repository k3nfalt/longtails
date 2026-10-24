import LongTails.Algorithms.ClusteredConvolutionalPerceptron
import LongTails.Proofs.ClusteredConvolutionalPerceptronGeometry
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ClusteredPerceptronLowerBound

open LongTails.Algorithms.ClusteredConvolutionalPerceptron

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma cluster_margin {e u z : E} {α q μ : ℝ}
    (he : ⟪e, e⟫ = 1) (heu : ⟪e, u⟫ = 0) (hez : ⟪e, z⟫ = 0) :
    ⟪α • e + μ • u, q • e + z⟫ = α * q + μ * ⟪u, z⟫ := by
  have hue : ⟪u, e⟫ = 0 := by rw [real_inner_comm, heu]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, he, hez, hue]
  ring

lemma residual_scaled_inner_bound {u z : E} {M : ℝ} (hu : ‖u‖ ≤ M) :
    |⟪u, z⟫| ≤ M * ‖z‖ :=
  (abs_real_inner_le_norm u z).trans (mul_le_mul_of_nonneg_right hu (norm_nonneg z))

lemma scaled_endpoint_signs {μ k β M : ℝ} {u v z : E}
    (hμ : 0 < μ) (hβ : β ≠ 0) (hk : 0 < k) (hM : 0 ≤ M)
    (hsmall : μ * M ^ 2 ≤ β ^ 2 / 4)
    (hu : ‖u‖ ≤ M) (hv : ‖v‖ ≤ M) (hz : ‖z‖ ≤ 2 * k * μ * M) :
    -k * μ * β ^ 2 + μ * ⟪u, z⟫ < 0 ∧
      (1 + μ) * (-k * μ * β ^ 2) + μ * ⟪v, z⟫ < 0 := by
  have hiu := (abs_le.mp (residual_scaled_inner_bound (z := z) hu)).2
  have hiv := (abs_le.mp (residual_scaled_inner_bound (z := z) hv)).2
  have hz' := mul_le_mul_of_nonneg_left hz hM
  have hu' := mul_le_mul_of_nonneg_left (hiu.trans hz') hμ.le
  have hv' := mul_le_mul_of_nonneg_left (hiv.trans hz') hμ.le
  have hkm : 0 < k * μ := mul_pos hk hμ
  have hnoise := mul_le_mul_of_nonneg_left hsmall hkm.le
  have hpos : 0 < k * μ * β ^ 2 := mul_pos hkm (sq_pos_of_ne_zero hβ)
  have hextra := mul_nonneg hμ.le hpos.le
  constructor <;> nlinarith

lemma scaled_after_positive_signs {μ k β M : ℝ} {u v z : E}
    (hμ : 0 < μ) (hμ1 : μ ≤ 1 / 4) (hβ : β ≠ 0) (hk : 0 ≤ k) (hM : 0 ≤ M)
    (hsmall : μ * M ^ 2 ≤ β ^ 2 / 4) (horizon : k * μ ≤ 1 / 4)
    (hu : ‖u‖ ≤ M) (hv : ‖v‖ ≤ M) (hz : ‖z‖ ≤ (2 * k + 1) * μ * M) :
    0 < (1 - k * μ) * β ^ 2 + μ * ⟪u, z⟫ ∧
      0 < (1 + μ) * (1 - k * μ) * β ^ 2 + μ * ⟪v, z⟫ := by
  have hiu := (abs_le.mp (residual_scaled_inner_bound (z := z) hu)).1
  have hiv := (abs_le.mp (residual_scaled_inner_bound (z := z) hv)).1
  have hz' := mul_le_mul_of_nonneg_left hz hM
  have hu' := mul_le_mul_of_nonneg_left hiu hμ.le
  have hv' := mul_le_mul_of_nonneg_left hiv hμ.le
  have hmz := mul_le_mul_of_nonneg_left hz' hμ.le
  have hfactor : (2 * k + 1) * μ ≤ 3 / 4 := by nlinarith
  have hfactor0 : 0 ≤ (2 * k + 1) * μ := by positivity
  have hnoise := mul_le_mul hfactor hsmall (by positivity : 0 ≤ μ * M ^ 2)
    (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have hbase := mul_le_mul_of_nonneg_right horizon (sq_nonneg β)
  have hpositive : 0 ≤ μ * (1 - k * μ) * β ^ 2 :=
    mul_nonneg (mul_nonneg hμ.le (by linarith)) (sq_nonneg β)
  constructor <;> nlinarith [sq_pos_of_ne_zero hβ]

lemma linear_pair_update {e u v z : E} {μ β M : ℝ} {k : ℕ}
    (he : ⟪e, e⟫ = 1) (heu : ⟪e, u⟫ = 0) (hev : ⟪e, v⟫ = 0) (hez : ⟪e, z⟫ = 0)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1 / 4) (hβ : β ≠ 0) (hM : 0 ≤ M)
    (hsmall : μ * M ^ 2 ≤ β ^ 2 / 4) (horizon : (k : ℝ) * μ ≤ 1 / 4)
    (hu : ‖u‖ ≤ M) (hv : ‖v‖ ≤ M) (hz : ‖z‖ ≤ 2 * k * μ * M) :
    let w := (-(k : ℝ) * μ * β) • e + z
    let pos := β • e + μ • u
    let neg := ((1 + μ) * β) • e + μ • v
    ⟪pos, w⟫ ≤ 0 ∧
      linearStep pos w = (β * (1 - k * μ)) • e + (z + μ • u) ∧
      ⟪-neg, linearStep pos w⟫ < 0 ∧
      linearStep (-neg) (linearStep pos w) =
        (-(k + 1 : ℝ) * μ * β) • e + (z + μ • u - μ • v) := by
  dsimp only
  have hfirst : ⟪β • e + μ • u, (-(k : ℝ) * μ * β) • e + z⟫ ≤ 0 := by
    rw [cluster_margin he heu hez]
    by_cases hk : k = 0
    · subst k
      have hz0 : z = 0 := norm_eq_zero.mp (le_antisymm (by simpa using hz) (norm_nonneg z))
      simp [hz0]
    · have h := (scaled_endpoint_signs hμ hβ (by exact_mod_cast Nat.pos_of_ne_zero hk)
        hM hsmall hu hv hz).1
      nlinarith
  have hpoint : linearStep (β • e + μ • u) ((-(k : ℝ) * μ * β) • e + z) =
      (β * (1 - k * μ)) • e + (z + μ • u) := by
    rw [linearStep, ite_eq_left hfirst]
    module
  have hcenter : ⟪e, z + μ • u⟫ = 0 := by
    simp only [inner_add_right, real_inner_smul_right, hez, heu, mul_zero, add_zero]
  have hnorm : ‖z + μ • u‖ ≤ (2 * k + 1) * μ * M := by
    have hn := norm_add_le z (μ • u)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμ] at hn
    have hm := mul_le_mul_of_nonneg_left hu hμ.le
    nlinarith
  have hsecond : ⟪-(((1 + μ) * β) • e + μ • v),
      linearStep (β • e + μ • u) ((-(k : ℝ) * μ * β) • e + z)⟫ < 0 := by
    rw [hpoint, inner_neg_left, cluster_margin he hev hcenter]
    have h := (scaled_after_positive_signs hμ hμ1 hβ (Nat.cast_nonneg k) hM hsmall
      horizon hu hv hnorm).2
    nlinarith
  refine ⟨hfirst, hpoint, hsecond, ?_⟩
  rw [linearStep, ite_eq_left hsecond.le, hpoint]
  module

lemma paired_linear_trace {n : ℕ} {e : E} {u v : Fin (n + 1) → E} {μ β M : ℝ}
    (he : ⟪e, e⟫ = 1) (heu : ∀ j, ⟪e, u j⟫ = 0) (hev : ∀ j, ⟪e, v j⟫ = 0)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1 / 4) (hβ : β ≠ 0) (hM : 0 ≤ M)
    (hsmall : μ * M ^ 2 ≤ β ^ 2 / 4) (hu : ∀ j, ‖u j‖ ≤ M) (hv : ∀ j, ‖v j‖ ≤ M) :
    ∀ k : ℕ, (k : ℝ) * μ ≤ 1 / 4 → ∃ z : E,
      pairedLinearIterate (fun j => β • e + μ • u j) (fun j => ((1 + μ) * β) • e + μ • v j) k =
        (-(k : ℝ) * μ * β) • e + z ∧ ⟪e, z⟫ = 0 ∧ ‖z‖ ≤ 2 * k * μ * M := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨0, ?_, ?_, ?_⟩ <;> simp [pairedLinearIterate]
  | succ k ih =>
    intro hk
    have hk' : (k : ℝ) * μ ≤ 1 / 4 := by
      push_cast at hk
      nlinarith
    obtain ⟨z, hz, hcenter, hnorm⟩ := ih hk'
    let j : Fin (n + 1) := ⟨k % (n + 1), Nat.mod_lt _ (by omega)⟩
    have hstep := linear_pair_update he (heu j) (hev j) hcenter hμ hμ1 hβ hM hsmall hk'
      (hu j) (hv j) hnorm
    dsimp only at hstep
    refine ⟨z + μ • u j - μ • v j, ?_, ?_, ?_⟩
    · rw [pairedLinearIterate, hz]
      simpa only [Nat.cast_add, Nat.cast_one] using hstep.2.2.2
    · simp only [inner_sub_right, inner_add_right, real_inner_smul_right, hcenter,
        heu j, hev j, mul_zero, add_zero, sub_zero]
    · have hn1 := norm_add_le z (μ • u j)
      have hn2 := norm_sub_le (z + μ • u j) (μ • v j)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμ] at hn1 hn2
      have hu' := mul_le_mul_of_nonneg_left (hu j) hμ.le
      have hv' := mul_le_mul_of_nonneg_left (hv j) hμ.le
      push_cast
      nlinarith

lemma paired_linear_mistakes {n : ℕ} {e : E} {u v : Fin (n + 1) → E} {μ β M : ℝ}
    (he : ⟪e, e⟫ = 1) (heu : ∀ j, ⟪e, u j⟫ = 0) (hev : ∀ j, ⟪e, v j⟫ = 0)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1 / 4) (hβ : β ≠ 0) (hM : 0 ≤ M)
    (hsmall : μ * M ^ 2 ≤ β ^ 2 / 4) (hu : ∀ j, ‖u j‖ ≤ M) (hv : ∀ j, ‖v j‖ ≤ M)
    (k : ℕ) (hk : (k : ℝ) * μ ≤ 1 / 4) :
    let pos := fun j => β • e + μ • u j
    let neg := fun j => ((1 + μ) * β) • e + μ • v j
    let j : Fin (n + 1) := ⟨k % (n + 1), Nat.mod_lt _ (by omega)⟩
    ⟪pos j, pairedLinearIterate pos neg k⟫ ≤ 0 ∧
      ⟪-neg j, pairedLinearMiddle pos neg k⟫ < 0 := by
  obtain ⟨z, hz, hc, hn⟩ := paired_linear_trace he heu hev hμ hμ1 hβ hM hsmall hu hv k hk
  dsimp only
  let j : Fin (n + 1) := ⟨k % (n + 1), Nat.mod_lt _ (by omega)⟩
  have hs := linear_pair_update he (heu j) (hev j) hc hμ hμ1 hβ hM hsmall hk (hu j) (hv j) hn
  dsimp only at hs
  rw [pairedLinearMiddle, hz]
  exact ⟨hs.1, hs.2.2.1⟩

open LongTails.Setups.ClusteredConvolutionalPerceptron (Features axis)
open LongTails.Setups.TwoSampleQuadraticPerceptron (shift)
open TwoSampleQuadraticPerceptronEmbedding
open ManySampleConvolutionalPerceptronGeometry (plusFeature minusFeature shift_axis axis_shift_inner axis_inner)
open ClusteredConvolutionalPerceptronGeometry (plus_norm_bound minus_norm_bound)

lemma frozen_feature_eq {d : ℕ} (κ : ℝ) (u : Features d) :
    frozenFeature κ u = (κ / 8) • plusFeature u + minusFeature u := by
  unfold frozenFeature plusFeature minusFeature
  module

lemma frozen_feature_norm {d : ℕ} {κ : ℝ} {u : Features d}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 4) (hu : ‖u‖ ≤ 2 / 3) : ‖frozenFeature κ u‖ ≤ 2 := by
  rw [frozen_feature_eq]
  have hp : ‖plusFeature u‖ ≤ 1 := by linarith [plus_norm_bound u]
  have hm : ‖minusFeature u‖ ≤ 1 := by linarith [minus_norm_bound u]
  have hn := norm_add_le ((κ / 8) • plusFeature u) (minusFeature u)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < κ / 8)] at hn
  have hmul := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ κ / 8)
  linarith

lemma frozen_feature_centered {d : ℕ} {u : Features d} (κ : ℝ) (hu : ⟪axis d, u⟫ = 0) :
    ⟪axis d, frozenFeature κ u⟫ = 0 := by
  simp only [frozenFeature, inner_add_right, real_inner_smul_right, axis_shift_inner,
    hu, mul_zero, add_zero]

lemma frozen_background {d : ℕ} (κ α μ : ℝ) (u : Features d) :
    frozenFeature κ (α • axis d + μ • u) =
      (α * (Real.sqrt 2 * κ / 8)) • axis d + μ • frozenFeature κ u := by
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have he : (κ / 8 + 1) / Real.sqrt 2 + (κ / 8 - 1) / Real.sqrt 2 = Real.sqrt 2 * κ / 8 := by
    field_simp
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    ring
  unfold frozenFeature
  rw [shift_add, shift_smul, shift_axis, shift_smul]
  calc
    _ = (α * ((κ / 8 + 1) / Real.sqrt 2 + (κ / 8 - 1) / Real.sqrt 2)) • axis d +
      μ • (((κ / 8 + 1) / Real.sqrt 2) • u + ((κ / 8 - 1) / Real.sqrt 2) • shift u) := by module
    _ = _ := by rw [he]

lemma frozen_linear_mistakes {d n : ℕ} {u v : Fin (n + 1) → Features d} {μ κ : ℝ}
    (hd : 0 < d) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 4) (hμ : 0 < μ)
    (hsmall : μ ≤ κ ^ 2 / 512)
    (heu : ∀ j, ⟪axis d, u j⟫ = 0) (hev : ∀ j, ⟪axis d, v j⟫ = 0)
    (hu : ∀ j, ‖u j‖ ≤ 2 / 3) (hv : ∀ j, ‖v j‖ ≤ 2 / 3)
    (k : ℕ) (hk : (k : ℝ) * μ ≤ 1 / 4) :
    let pos := fun j => frozenFeature κ (axis d + μ • u j)
    let neg := fun j => frozenFeature κ ((1 + μ) • axis d + μ • v j)
    let j : Fin (n + 1) := ⟨k % (n + 1), Nat.mod_lt _ (by omega)⟩
    ⟪pos j, pairedLinearIterate pos neg k⟫ ≤ 0 ∧
      ⟪-neg j, pairedLinearMiddle pos neg k⟫ < 0 := by
  have hβ : Real.sqrt 2 * κ / 8 ≠ 0 := by positivity
  have hβ2 : (Real.sqrt 2 * κ / 8) ^ 2 = κ ^ 2 / 32 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [mul_nonneg (sq_nonneg κ) (sq_nonneg (Real.sqrt 2))]
  have hμ1 : μ ≤ 1 / 4 := by nlinarith
  have hsmall' : μ * (2 : ℝ) ^ 2 ≤ (Real.sqrt 2 * κ / 8) ^ 2 / 4 := by
    rw [hβ2]
    nlinarith
  have h := paired_linear_mistakes (axis_inner hd)
    (fun j => frozen_feature_centered κ (heu j)) (fun j => frozen_feature_centered κ (hev j))
    hμ hμ1 hβ (by norm_num : (0 : ℝ) ≤ 2) hsmall'
    (fun j => frozen_feature_norm hκ hκ1 (hu j)) (fun j => frozen_feature_norm hκ hκ1 (hv j)) k hk
  have hpos : (fun j => frozenFeature κ (axis d + μ • u j)) =
      (fun j => (Real.sqrt 2 * κ / 8) • axis d + μ • frozenFeature κ (u j)) := by
    funext j
    simpa using frozen_background κ 1 μ (u j)
  have hneg : (fun j => frozenFeature κ ((1 + μ) • axis d + μ • v j)) =
      (fun j => ((1 + μ) * (Real.sqrt 2 * κ / 8)) • axis d + μ • frozenFeature κ (v j)) := by
    funext j
    exact frozen_background κ (1 + μ) μ (v j)
  dsimp only
  rw [hpos, hneg, congrFun hpos ⟨k % (n + 1), Nat.mod_lt _ (by omega)⟩,
    congrFun hneg ⟨k % (n + 1), Nat.mod_lt _ (by omega)⟩]
  exact h

end LongTails.Proofs.ClusteredPerceptronLowerBound
