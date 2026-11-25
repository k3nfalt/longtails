import LongTails.Setups.CenteredLogisticClassification
import LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.CenteredLogisticGeometry

open LongTails.Setups.CenteredLogisticClassification
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)

section Means

variable {ι : Type*} [Fintype ι] {d : ℕ}

local notation "E" => Features d

lemma mean_norm_le [Nonempty ι] {f : ι → E} {M : ℝ} (h : ∀ i, ‖f i‖ ≤ M) : ‖𝔼 i, f i‖ ≤ M := by
  refine le_trans (Finset.le_expect_of_subadditive norm_zero norm_add_le ?_) ?_
  · intro q x
    simp only [← NNRat.cast_smul_eq_nnqsmul ℝ, norm_smul, Real.norm_eq_abs,
      smul_eq_mul]
    rw [abs_of_nonneg (by positivity)]
  · exact Finset.expect_le Finset.univ_nonempty (fun i _ => h i)

lemma mean_varying_smul (a : ι → ℝ) (v : E) :
    (𝔼 i, a i • v) = (𝔼 i, a i) • v :=
  (map_expect ((LinearMap.toSpanSingleton ℝ E v).restrictScalars ℚ≥0) a Finset.univ).symm

lemma mean_inner (v : E) (f : ι → E) : (𝔼 i, ⟪v, f i⟫) = ⟪v, 𝔼 i, f i⟫ :=
  (map_expect (((innerSL ℝ v).toLinearMap).restrictScalars ℚ≥0) f Finset.univ).symm

end Means

variable {p : Params} {D : Data p} (G : Geometry p D)

noncomputable def row (i : Fin p.n) : Features p.d := G.y i • (G.level • G.axis + G.h i)

noncomputable def signal : Features p.d := 𝔼 i, row G i

noncomputable def tangent : Features p.d := signal G - ⟪G.axis, signal G⟫ • G.axis

lemma row_scale (i : Fin p.n) : D i = G.R • row G i := by
  rw [G.sample_eq, row, smul_smul, mul_comm]

lemma mean_row : (𝔼 i, row G i) = signal G := rfl

lemma signal_norm : ‖signal G‖ ≤ G.ε := G.mean_bound

lemma variance_nonneg : 0 ≤ 𝔼 i, ‖G.h i‖ ^ 2 :=
  Finset.expect_nonneg (fun _ _ => sq_nonneg _)

lemma variance_le : (𝔼 i, ‖G.h i‖ ^ 2) ≤ G.ε ^ 2 :=
  Finset.expect_le Finset.univ_nonempty (fun i _ => by
    exact pow_le_pow_left₀ (norm_nonneg _) (G.radius i) _)

lemma abs_level : |G.level| ≤ 1 := by
  nlinarith [G.normalized, variance_nonneg G, sq_abs G.level, abs_nonneg G.level]

lemma row_norm (i : Fin p.n) : ‖row G i‖ ≤ 33 / 32 := by
  simp only [row, norm_smul, Real.norm_eq_abs, G.labels, one_mul]
  have h := norm_add_le (G.level • G.axis) (G.h i)
  rw [norm_smul, Real.norm_eq_abs, G.axis_unit, mul_one] at h
  linarith [abs_level G, G.radius i, G.radius_le]

lemma row_energy : (𝔼 i, ‖row G i‖ ^ 2) = 1 := by
  have h (i : Fin p.n) : ‖row G i‖ ^ 2 =
      G.level ^ 2 + (2 * G.level * ⟪G.axis, G.h i⟫ + ‖G.h i‖ ^ 2) := by
    simp only [row, norm_smul, Real.norm_eq_abs, G.labels, one_mul, norm_add_sq_real,
      norm_smul, G.axis_unit, mul_one, sq_abs, real_inner_smul_left]
    ring
  simp_rw [h]
  rw [Finset.expect_add_distrib, Fintype.expect_const, Finset.expect_add_distrib,
    ← Finset.mul_expect, mean_inner, G.centered, inner_zero_right, mul_zero, zero_add]
  exact G.normalized

lemma axis_tangent : ⟪G.axis, tangent G⟫ = 0 := by
  simp [tangent, inner_sub_right, real_inner_smul_right, G.axis_unit]

lemma tangent_norm : ‖tangent G‖ ≤ G.ε := by
  have hproj : ‖tangent G‖ ^ 2 = ‖signal G‖ ^ 2 - ⟪G.axis,signal G⟫ ^ 2 := by
    rw [tangent, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, G.axis_unit, mul_one,
      sq_abs, real_inner_smul_right, real_inner_comm G.axis (signal G)]
    ring
  nlinarith [sq_nonneg ⟪G.axis,signal G⟫, pow_le_pow_left₀ (norm_nonneg _) (signal_norm G) 2,
    norm_nonneg (tangent G), G.radius_pos]

lemma reflected_norm : ‖(2 : ℝ) • tangent G - signal G‖ = ‖signal G‖ := by
  have he : (2 : ℝ) • tangent G - signal G =
      signal G - (2 * ⟪G.axis,signal G⟫) • G.axis := by unfold tangent; module
  have hsq : ‖(2 : ℝ) • tangent G - signal G‖ ^ 2 = ‖signal G‖ ^ 2 := by
    rw [he, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, G.axis_unit, mul_one, sq_abs,
      real_inner_smul_right, real_inner_comm G.axis (signal G)]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

lemma row_tangent (i : Fin p.n) : ⟪row G i, tangent G⟫ = G.y i * ⟪G.h i, tangent G⟫ := by
  simp [row, real_inner_smul_left, inner_add_left, axis_tangent]

lemma covariance_split (v : Features p.d) :
    (𝔼 i, ⟪row G i, v⟫ • row G i) =
      (G.level ^ 2 * ⟪G.axis, v⟫) • G.axis + (𝔼 i, ⟪G.h i, v⟫ • G.h i) := by
  have hi (i : Fin p.n) : ⟪row G i, v⟫ • row G i =
      (G.level ^ 2 * ⟪G.axis, v⟫) • G.axis +
      ((G.level * ⟪G.axis, v⟫) • G.h i +
      (⟪v, G.h i⟫ • (G.level • G.axis) + ⟪G.h i, v⟫ • G.h i)) := by
    have hy : G.y i * G.y i = 1 := by nlinarith [sq_abs (G.y i), G.labels i]
    rw [row, real_inner_smul_left, smul_smul, mul_right_comm, hy, one_mul,
      inner_add_left, real_inner_smul_left, real_inner_comm v (G.h i)]
    module
  simp_rw [hi]
  rw [Finset.expect_add_distrib, Fintype.expect_const, Finset.expect_add_distrib,
    ← Finset.smul_expect, G.centered, smul_zero, zero_add, Finset.expect_add_distrib,
    mean_varying_smul, mean_inner, G.centered, inner_zero_right, zero_smul, zero_add]

end LongTails.Proofs.CenteredLogisticGeometry
