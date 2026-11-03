import LongTails.Algorithms.DerivativeConvolutionalPerceptron
import LongTails.Proofs.ClusteredPerceptronLowerBound

open scoped RealInnerProductSpace

namespace LongTails.Proofs.DerivativePerceptronLowerBound

open LongTails.Algorithms.DerivativeConvolutionalPerceptron
open LongTails.Algorithms.ClusteredConvolutionalPerceptron (linearStep pairedLinearIterate pairedLinearMiddle)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma frozenStep_scale (η : ℝ) (hη : 0 < η) (v w : E) :
    frozenStep η v (η • w) = η • linearStep v w := by
  have hs : η * ⟪v, w⟫ ≤ 0 ↔ ⟪v, w⟫ ≤ 0 := by
    constructor
    · intro hh
      nlinarith only [hh, hη]
    · exact mul_nonpos_of_nonneg_of_nonpos hη.le
  simp only [frozenStep, linearStep, real_inner_smul_right, hs]
  split_ifs <;> module

lemma frozenPairedIterate_scale {n : ℕ} (η : ℝ) (hη : 0 < η)
    (positive negative : Fin (n + 1) → E) (k : ℕ) :
    frozenPairedIterate η positive negative k = η • pairedLinearIterate positive negative k := by
  induction k with
  | zero => simp [frozenPairedIterate, pairedLinearIterate]
  | succ k ih =>
    simp only [frozenPairedIterate, pairedLinearIterate, ih, frozenStep_scale η hη]

lemma frozenPairedMiddle_scale {n : ℕ} (η : ℝ) (hη : 0 < η)
    (positive negative : Fin (n + 1) → E) (k : ℕ) :
    frozenPairedMiddle η positive negative k = η • pairedLinearMiddle positive negative k := by
  simp only [frozenPairedMiddle, pairedLinearMiddle, frozenPairedIterate_scale η hη,
    frozenStep_scale η hη]

lemma paired_mistakes {n : ℕ} {e : E} {u v : Fin (n + 1) → E} {μ β M η : ℝ}
    (he : ⟪e, e⟫ = 1) (heu : ∀ j, ⟪e, u j⟫ = 0) (hev : ∀ j, ⟪e, v j⟫ = 0)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1 / 4) (hβ : β ≠ 0) (hM : 0 ≤ M) (hη : 0 < η)
    (hsmall : μ * M ^ 2 ≤ β ^ 2 / 4) (hu : ∀ j, ‖u j‖ ≤ M) (hv : ∀ j, ‖v j‖ ≤ M)
    (k : ℕ) (hk : (k : ℝ) * μ ≤ 1 / 4) :
    let pos := fun j => β • e + μ • u j
    let neg := fun j => ((1 + μ) * β) • e + μ • v j
    let j : Fin (n + 1) := ⟨k % (n + 1), Nat.mod_lt _ (by omega)⟩
    ⟪pos j, frozenPairedIterate η pos neg k⟫ ≤ 0 ∧
      ⟪-neg j, frozenPairedMiddle η pos neg k⟫ < 0 := by
  have hm := ClusteredPerceptronLowerBound.paired_linear_mistakes
    he heu hev hμ hμ1 hβ hM hsmall hu hv k hk
  dsimp only at hm ⊢
  rw [frozenPairedIterate_scale η hη, frozenPairedMiddle_scale η hη,
    real_inner_smul_right, real_inner_smul_right]
  exact ⟨mul_nonpos_of_nonneg_of_nonpos hη.le hm.1, mul_neg_of_pos_of_neg hη hm.2⟩

open LongTails.Setups.DerivativeConvolutionalPerceptron (Features axis)

lemma frozen_margin {d : ℕ} (b w : Features d) :
    LongTails.Setups.TwoSampleQuadraticPerceptron.margin .conv d b ((Real.sqrt 2, 0), w) =
      ⟪frozenFeature b, w⟫ := by
  simp [LongTails.Setups.TwoSampleQuadraticPerceptron.margin, frozenFeature, real_inner_smul_left]

lemma frozen_head_direction {d : ℕ} (b w : Features d) :
    (LongTails.Setups.TwoSampleQuadraticPerceptron.direction .conv d b ((Real.sqrt 2, 0), w)).2 =
      frozenFeature b := by
  simp [LongTails.Setups.TwoSampleQuadraticPerceptron.direction, frozenFeature]

lemma frozen_feature_norm {d : ℕ} {u : Features d} (hu : ‖u‖ ≤ 1 / 2) :
    ‖frozenFeature u‖ ≤ 1 := by
  have hs := Real.sqrt_nonneg (2 : ℝ)
  have hs₂ : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), hs]
  have hm := mul_le_mul_of_nonneg_left hu hs
  simp only [frozenFeature, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  nlinarith only [hm, hs₂]

lemma frozen_mistakes {d n : ℕ} {u v : Fin (n + 1) → Features d} {μ η : ℝ}
    (hd : 0 < d) (hμ : 0 < μ) (hμ₁ : μ ≤ 1 / 4) (hη : 0 < η)
    (heu : ∀ j, ⟪axis d, u j⟫ = 0) (hev : ∀ j, ⟪axis d, v j⟫ = 0)
    (hu : ∀ j, ‖u j‖ ≤ 1 / 2) (hv : ∀ j, ‖v j‖ ≤ 1 / 2)
    (k : ℕ) (hk : (k : ℝ) * μ ≤ 1 / 4) :
    let pos := fun j => frozenFeature (axis d + μ • u j)
    let neg := fun j => frozenFeature ((1 + μ) • axis d - μ • v j)
    let j : Fin (n + 1) := ⟨k % (n + 1), Nat.mod_lt _ (by omega)⟩
    ⟪pos j, frozenPairedIterate η pos neg k⟫ ≤ 0 ∧
      ⟪-neg j, frozenPairedMiddle η pos neg k⟫ < 0 := by
  have heu' : ∀ j, ⟪axis d, frozenFeature (u j)⟫ = 0 := by
    intro j
    simp only [frozenFeature, real_inner_smul_right, heu, mul_zero]
  have hev' : ∀ j, ⟪axis d, -frozenFeature (v j)⟫ = 0 := by
    intro j
    simp only [inner_neg_right, frozenFeature, real_inner_smul_right, hev, mul_zero, neg_zero]
  have hβ : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hsmall : μ * (1 : ℝ) ^ 2 ≤ Real.sqrt 2 ^ 2 / 4 := by
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    nlinarith only [hμ₁]
  have hm := paired_mistakes (ManySampleConvolutionalPerceptronGeometry.axis_inner hd)
    heu' hev' hμ hμ₁ hβ (by norm_num : (0 : ℝ) ≤ 1) hη hsmall
    (fun j => frozen_feature_norm (hu j))
    (fun j => by simpa only [norm_neg] using frozen_feature_norm (hv j)) k hk
  have hp : (fun j => Real.sqrt 2 • axis d + μ • frozenFeature (u j)) =
      (fun j => frozenFeature (axis d + μ • u j)) := by
    funext j
    unfold frozenFeature
    module
  have hn : (fun j => ((1 + μ) * Real.sqrt 2) • axis d + μ • -frozenFeature (v j)) =
      (fun j => frozenFeature ((1 + μ) • axis d - μ • v j)) := by
    funext j
    unfold frozenFeature
    module
  dsimp only at hm ⊢
  rw [hp, hn] at hm
  have hpj := congrFun hp (⟨k % (n + 1), Nat.mod_lt _ (by omega)⟩ : Fin (n + 1))
  have hnj := congrFun hn (⟨k % (n + 1), Nat.mod_lt _ (by omega)⟩ : Fin (n + 1))
  rw [hpj, hnj] at hm
  exact hm

end LongTails.Proofs.DerivativePerceptronLowerBound
