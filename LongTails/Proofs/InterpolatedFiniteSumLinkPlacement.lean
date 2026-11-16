import LongTails.Proofs.InterpolatedFiniteSumExponentialFamily

open scoped BigOperators RealInnerProductSpace
open Classical

namespace LongTails.Proofs.InterpolatedFiniteSumLinkPlacement

variable {I J V : Type*}

noncomputable def assigned (θ : I ↪ J) (f : I → V) (z : V) (i : J) : V :=
  Function.extend θ f (fun _ => z) i

lemma assigned_at (θ : I ↪ J) (f : I → V) (z : V) (j : I) : assigned θ f z (θ j) = f j :=
  θ.injective.extend_apply f (fun _ => z) j

lemma assigned_outside (θ : I ↪ J) (f : I → V) (z : V) (i : J) (hi : ¬∃ j, θ j = i) :
    assigned θ f z i = z := Function.extend_apply' f (fun _ => z) i hi

lemma assigned_property (θ : I ↪ J) (f : I → V) (z : V) (P : V → Prop)
    (hf : ∀ j, P (f j)) (hz : P z) (i : J) : P (assigned θ f z i) := by
  by_cases hi : ∃ j, θ j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [assigned_at]
    exact hf j
  · rw [assigned_outside θ f z i hi]
    exact hz

lemma sum_assigned_lower [Fintype I] [Fintype J] (θ : I ↪ J) (f : I → V) (z : V)
    (H : V → ℝ) (hz : 0 ≤ H z) : (∑ j : I, H (f j)) ≤ ∑ i : J, H (assigned θ f z i) := by
  have he : (∑ i ∈ Finset.univ.image θ, H (assigned θ f z i)) = ∑ j : I, H (f j) := by
    rw [Finset.sum_image (fun _ _ _ _ h => θ.injective h)]
    simp only [assigned_at]
  rw [← he]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro i _ hi
  have hh : ¬∃ j, θ j = i := by simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hi
  rw [assigned_outside θ f z i hh]
  exact hz

lemma sum_assigned_eq [Fintype I] [Fintype J] (θ : I ↪ J) (f : I → V) (z : V)
    (H : V → ℝ) (hz : H z = 0) : (∑ i : J, H (assigned θ f z i)) = ∑ j : I, H (f j) := by
  have he : (∑ i ∈ Finset.univ.image θ, H (assigned θ f z i)) = ∑ j : I, H (f j) := by
    rw [Finset.sum_image (fun _ _ _ _ h => θ.injective h)]
    simp only [assigned_at]
  rw [← he]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hh : ¬∃ j, θ j = i := by simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hi
  rw [assigned_outside θ f z i hh, hz]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma assigned_gradient (θ : I ↪ J) (f : I → E → ℝ) (df : I → E → E)
    (z : E → ℝ) (dz : E → E) (hf : ∀ j x, HasGradientAt (f j) (df j x) x)
    (hz : ∀ x, HasGradientAt z (dz x) x) (i : J) (x : E) :
    HasGradientAt (assigned θ f z i) (assigned θ df dz i x) x := by
  by_cases hi : ∃ j, θ j = i
  · obtain ⟨j, rfl⟩ := hi
    simp only [assigned_at]
    exact hf j x
  · simp only [assigned_outside θ _ _ i hi]
    exact hz x

end LongTails.Proofs.InterpolatedFiniteSumLinkPlacement
