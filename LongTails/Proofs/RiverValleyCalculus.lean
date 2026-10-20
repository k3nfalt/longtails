import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

open Set Filter Topology

namespace OracleTemplate.RiverValley

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma segment_deriv {g : E → V} {Dg : E → E →L[ℝ] V} (hg : ∀ y, HasFDerivAt g (Dg y) y)
    (y d : E) (t : ℝ) : HasDerivAt (fun s : ℝ => g (y + s • d)) (Dg (y + t • d) d) t := by
  have h1 : HasDerivAt (fun s : ℝ => y + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add y
  exact (hg (y + t • d)).comp_hasDerivAt t h1

lemma taylor_lip {g : E → V} {Dg : E → E →L[ℝ] V} (hg : ∀ y, HasFDerivAt g (Dg y) y)
    {c : ℝ} (hc : 0 ≤ c) (hD : ∀ y y', ‖Dg y - Dg y'‖ ≤ c * ‖y - y'‖) (y d : E) :
    ‖g (y + d) - g y - Dg y d‖ ≤ c * ‖d‖ ^ 2 := by
  let ψ : ℝ → V := fun t => g (y + t • d) - t • Dg y d
  have hψ : ∀ t, HasDerivAt ψ (Dg (y + t • d) d - Dg y d) t := by
    intro t
    have h3 : HasDerivAt (fun t : ℝ => t • Dg y d) (Dg y d) t := by
      simpa using (hasDerivAt_id t).smul_const (Dg y d)
    exact (segment_deriv hg y d t).sub h3
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖Dg (y + t • d) d - Dg y d‖ ≤ c * ‖d‖ ^ 2 := by
    intro t ht
    have e : Dg (y + t • d) d - Dg y d = (Dg (y + t • d) - Dg y) d := by simp
    rw [e]
    calc ‖(Dg (y + t • d) - Dg y) d‖ ≤ ‖Dg (y + t • d) - Dg y‖ * ‖d‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * ‖(y + t • d) - y‖ * ‖d‖ := mul_le_mul_of_nonneg_right (hD _ _) (norm_nonneg _)
      _ = c * t * ‖d‖ ^ 2 := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]; ring
      _ ≤ c * 1 * ‖d‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left ht.2.le hc
      _ = c * ‖d‖ ^ 2 := by ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := ψ) (fun t _ => (hψ t).hasDerivWithinAt) hbound
  have e1 : ψ 1 - ψ 0 = g (y + d) - g y - Dg y d := by
    simp only [ψ, one_smul, zero_smul, add_zero, sub_zero]; abel
  rw [e1] at key
  exact key

lemma deriv_norm_le {g : E → V} {Dg : E → E →L[ℝ] V} (hg : ∀ y, HasFDerivAt g (Dg y) y)
    {c : ℝ} (hc : 0 ≤ c) (hlip : ∀ y y', ‖g y - g y'‖ ≤ c * ‖y - y'‖) (y : E) : ‖Dg y‖ ≤ c :=
  (hg y).le_of_lip' hc (Eventually.of_forall fun z => hlip z y)

lemma diff_le_of_dir {g : E → V} {Dg : E → E →L[ℝ] V} (hg : ∀ y, HasFDerivAt g (Dg y) y)
    {c : ℝ} (y d : E) (hd : ∀ z, ‖Dg z d‖ ≤ c * ‖d‖) : ‖g (y + d) - g y‖ ≤ c * ‖d‖ := by
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => g (y + s • d)) (fun t _ => (segment_deriv hg y d t).hasDerivWithinAt)
    (fun t _ => hd _)
  simpa using key

lemma deriv_mem {K : Submodule ℝ V} (hK : IsClosed (K : Set V)) {g : E → V}
    {Dg : E → E →L[ℝ] V} (hg : ∀ y, HasFDerivAt g (Dg y) y) (hgK : ∀ y, g y ∈ K) (y z : E) :
    Dg y z ∈ K := by
  have hd : HasDerivAt (fun s : ℝ => g (y + s • z)) (Dg y z) 0 := by
    simpa using segment_deriv hg y z 0
  have ht := hd.tendsto_slope_zero
  refine hK.mem_of_tendsto ht (Eventually.of_forall fun t => ?_)
  exact K.smul_mem _ (K.sub_mem (hgK _) (hgK _))

end OracleTemplate.RiverValley
