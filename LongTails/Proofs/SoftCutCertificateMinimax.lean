import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

open scoped BigOperators

namespace LongTails.Proofs.SoftCutCertificateMinimax

lemma capped_certificate_exists {ι E : Type*} [Fintype ι]
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (Y : Set E) (hY : Y.Nonempty) (hYconv : Convex ℝ Y) (hYcompact : IsCompact Y)
    (ℓ : E → ι → ℝ) (hcontinuous : ∀ i, Continuous (fun y => ℓ y i))
    (hconvex : ∀ i, ConvexOn ℝ Y (fun y => ℓ y i))
    (margin : ℝ) (hmargin : ∀ y ∈ Y, margin ≤ ∑ i, max 0 (ℓ y i)) :
    ∃ θ : ι → ℝ, (∀ i, 0 ≤ θ i ∧ θ i ≤ 1) ∧
      ∀ y ∈ Y, margin ≤ ∑ i, θ i * ℓ y i := by
  classical
  let C : Set (ι → ℝ) := Set.Icc 0 1
  let F : E → (ι → ℝ) → ℝ := fun y θ => ∑ i, θ i * ℓ y i
  have hC : C.Nonempty := ⟨0, by simp [C]⟩
  have hCconv : Convex ℝ C := convex_Icc 0 1
  have hCcompact : IsCompact C := isCompact_Icc
  have hleft (θ : ι → ℝ) : Continuous (fun y => F y θ) := by
    dsimp [F]
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (hcontinuous i)
  have hleftconv (θ : ι → ℝ) (hθ : θ ∈ C) : ConvexOn ℝ Y (fun y => F y θ) := by
    refine ⟨hYconv, ?_⟩
    intro x hx y hy a b ha hb hab
    change (∑ i, θ i * ℓ (a • x + b • y) i) ≤
      a * (∑ i, θ i * ℓ x i) + b * (∑ i, θ i * ℓ y i)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_left ((hconvex i).2 hx hy ha hb hab) (hθ.1 i)
    simpa only [smul_eq_mul, mul_add, mul_left_comm] using h
  have hright (y : E) : Continuous (F y) := by
    dsimp [F]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const
  have hrightconc (y : E) : ConcaveOn ℝ C (F y) := by
    refine ⟨hCconv, ?_⟩
    intro θ hθ ψ hψ a b ha hb hab
    change a * (∑ i, θ i * ℓ y i) + b * (∑ i, ψ i * ℓ y i) ≤
      ∑ i, (a * θ i + b * ψ i) * ℓ y i
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    apply le_of_eq
    ring
  obtain ⟨a, ha, θ, hθ, hsaddle⟩ := Sion.exists_isSaddlePointOn hY hYconv hYcompact
    (fun θ _ => (hleft θ).continuousOn.lowerSemicontinuousOn)
    (fun θ hθ => (hleftconv θ hθ).quasiconvexOn)
    hCconv hC hCcompact
    (fun y _ => (hright y).continuousOn.upperSemicontinuousOn)
    (fun y _ => (hrightconc y).quasiconcaveOn)
  refine ⟨θ, fun i => ⟨hθ.1 i, hθ.2 i⟩, ?_⟩
  let ψ : ι → ℝ := fun i => if 0 ≤ ℓ a i then 1 else 0
  have hψ : ψ ∈ C := by
    constructor <;> intro i <;> dsimp [ψ] <;> split_ifs <;> norm_num
  have hpositive : (∑ i, max 0 (ℓ a i)) = F a ψ := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [ψ]
    split_ifs with hi
    · simp [max_eq_right hi]
    · simp [max_eq_left (le_of_not_ge hi)]
  intro y hy
  exact (hmargin a ha).trans (hpositive ▸ hsaddle y hy ψ hψ)

end LongTails.Proofs.SoftCutCertificateMinimax
