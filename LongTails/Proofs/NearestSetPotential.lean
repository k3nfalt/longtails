import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

open Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.NearestSet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def potential (M : Set E) (x : E) : ℝ :=
  (‖x‖ ^ 2 - infDist x M ^ 2) / 2

noncomputable def divergence (M : Set E) (p x y : E) : ℝ :=
  potential M x - potential M y - ⟪p, x - y⟫

lemma potential_support {M : Set E} {p : E} (hp : p ∈ M) (x : E) :
    ⟪x, p⟫ - ‖p‖ ^ 2 / 2 ≤ potential M x := by
  have h := pow_le_pow_left₀ (infDist_nonneg : 0 ≤ infDist x M)
    (infDist_le_dist_of_mem hp) 2
  rw [dist_eq_norm, norm_sub_sq_real] at h
  unfold potential
  nlinarith

lemma potential_eq_support {M : Set E} {x p : E}
    (hp : infDist x M = ‖x - p‖) :
    potential M x = ⟪x, p⟫ - ‖p‖ ^ 2 / 2 := by
  unfold potential
  rw [hp, norm_sub_sq_real]
  ring

lemma divergence_nonneg {M : Set E} {y p : E} (hp : p ∈ M)
    (hnear : infDist y M = ‖y - p‖) (x : E) :
    0 ≤ divergence M p x y := by
  have h := potential_support hp x
  unfold divergence
  rw [potential_eq_support hnear, inner_sub_right, ← real_inner_comm p x,
    ← real_inner_comm p y]
  linarith

lemma divergence_eq_dist {M : Set E} {y p : E}
    (hnear : infDist y M = ‖y - p‖) (x : E) :
    divergence M p x y = (‖x - p‖ ^ 2 - infDist x M ^ 2) / 2 := by
  unfold divergence
  rw [potential_eq_support hnear, inner_sub_right, ← real_inner_comm p x,
    ← real_inner_comm p y, norm_sub_sq_real]
  unfold potential
  ring

lemma potential_convex [ProperSpace E] {M : Set E} (hM : IsClosed M)
    (hne : M.Nonempty) : ConvexOn ℝ univ (potential M) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  obtain ⟨p, hp, hnear⟩ := hM.exists_infDist_eq_dist hne (a • x + b • y)
  rw [dist_eq_norm] at hnear
  rw [potential_eq_support hnear]
  have hx := mul_le_mul_of_nonneg_left (potential_support hp x) ha
  have hy := mul_le_mul_of_nonneg_left (potential_support hp y) hb
  simp only [inner_add_left, real_inner_smul_left, smul_eq_mul]
  have he := congrArg (fun t : ℝ => t * (‖p‖ ^ 2 / 2)) hab
  nlinarith only [hx, hy, he]

lemma divergence_convex [ProperSpace E] {M : Set E} (hM : IsClosed M)
    (hne : M.Nonempty) (p y : E) : ConvexOn ℝ univ (fun x => divergence M p x y) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  have h := (potential_convex hM hne).2 (mem_univ x) (mem_univ z) ha hb hab
  simp only [divergence, inner_sub_right, inner_add_right, inner_smul_right,
    smul_eq_mul] at h ⊢
  have he := congrArg (fun t : ℝ => t * (potential M y - ⟪p, y⟫)) hab
  nlinarith only [h, he]

lemma divergence_three_point (M : Set E) (p q x y z : E) :
    divergence M q x z - divergence M p x y - divergence M q y z =
      ⟪p - q, x - y⟫ := by
  simp only [divergence, inner_sub_left, inner_sub_right]
  ring

end OracleTemplate.NearestSet
