import LongTails.Setups.RidgeClockTwoTapLogistic
import LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoTapImageSeparation

open LongTails.Setups.RidgeClockTwoTapLogistic
open LongTails.Setups.TwoSampleQuadraticPerceptron (shift Features Space margin)
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding (shift_add shift_smul)

lemma excludes_fit {u : Input} (X : Rows u) (q : Fin u.n → ℝ)
    (hn : ∀ i, 0 ≤ q i) (hp : ∃ i, 0 < q i) (hz : ∑ i, q i • X i = 0)
    (z : Space .conv u.d) : ¬separates X z := by
  let L : Features u.d →ₗ[ℝ] Features u.d :=
    { toFun := shift, map_add' := shift_add, map_smul' := shift_smul }
  have hs := congrArg L hz
  simp only [map_sum,map_smul,map_zero] at hs
  have s₁ := congrArg (fun x : Features u.d => ⟪x,z.2⟫) hz
  have s₂ := congrArg (fun x : Features u.d => ⟪x,z.2⟫) hs
  simp only [sum_inner,real_inner_smul_left,inner_zero_left] at s₁ s₂
  intro hit
  obtain ⟨j,hj⟩ := hp
  have h : 0 < ∑ i, q i * margin .conv u.d (X i) z :=
    Finset.sum_pos' (fun i _ => mul_nonneg (hn i) (hit i).le)
      ⟨j,Finset.mem_univ _,mul_pos hj (hit j)⟩
  have he : (∑ i, q i * margin .conv u.d (X i) z) =
      z.1.1*(∑ i, q i*⟪X i,z.2⟫)+z.1.2*(∑ i, q i*⟪L (X i),z.2⟫) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by dsimp [L,margin]; ring
  rw [he,s₁,s₂] at h
  linarith

end LongTails.Proofs.TwoTapImageSeparation
