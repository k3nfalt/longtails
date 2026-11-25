import LongTails.Proofs.CyclicLogisticTuning

open scoped RealInnerProductSpace
open LongTails.Setups.CyclicLogisticFeatureLearning
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift)
open LongTails.Proofs.CyclicLogisticGroups
open LongTails.Proofs.CyclicLogisticDynamics
open LongTails.Proofs.CyclicLogisticTrajectory

namespace LongTails.Proofs.CyclicLogisticCoordinates

variable {d : ℕ}

noncomputable def physical : Point (Features d) →ₗ[ℝ] ((ℝ × ℝ) × Features d) where
  toFun s := (((Real.sqrt 2)⁻¹ * (s.fst.fst + s.snd.fst),
    (Real.sqrt 2)⁻¹ * (s.fst.fst - s.snd.fst)), s.fst.snd + s.snd.snd)
  map_add' s t := by
    apply Prod.ext
    · apply Prod.ext <;> dsimp <;> ring
    · dsimp
      abel
  map_smul' c s := by
    apply Prod.ext
    · apply Prod.ext <;> dsimp <;> ring
    · dsimp
      rw [smul_add]

lemma physical_initial : physical (initial : Point (Features d)) = ((1, 0), 0) := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  apply Prod.ext
  · apply Prod.ext
    · change (Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹ + (Real.sqrt 2)⁻¹) = 1
      field_simp
      nlinarith
    · change (Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹ - (Real.sqrt 2)⁻¹) = 0
      rw [sub_self, mul_zero]
  · exact add_zero _

def Aligned (b : Features d) (s : Point (Features d)) : Prop :=
  ⟪sumFeature b, s.snd.snd⟫ = 0 ∧ ⟪diffFeature b, s.fst.snd⟫ = 0

private lemma aligned_parts (b : Features d) (s : Point (Features d)) (h : Aligned b s) :
    ⟪shift b, s.snd.snd⟫ = -⟪b, s.snd.snd⟫ ∧ ⟪shift b, s.fst.snd⟫ = ⟪b, s.fst.snd⟫ := by
  obtain ⟨hu, hv⟩ := h
  have hc : (Real.sqrt 2)⁻¹ ≠ 0 := by positivity
  simp only [sumFeature, diffFeature, real_inner_smul_left, inner_add_left, inner_sub_left,
    mul_eq_zero, hc, false_or] at hu hv
  constructor <;> linarith

lemma physical_score (b : Features d) (s : Point (Features d)) (h : Aligned b s) :
    LongTails.Setups.TwoSampleQuadraticPerceptron.margin .conv d b (physical s) =
      margin (sumFeature b) (diffFeature b) s := by
  obtain ⟨hu, hv⟩ := aligned_parts b s h
  change ((Real.sqrt 2)⁻¹ * (s.fst.fst + s.snd.fst)) * ⟪b, s.fst.snd + s.snd.snd⟫ +
    ((Real.sqrt 2)⁻¹ * (s.fst.fst - s.snd.fst)) * ⟪shift b, s.fst.snd + s.snd.snd⟫ = _
  simp only [margin, value, sumFeature, diffFeature, real_inner_smul_left, inner_add_left,
    inner_sub_left, inner_add_right, hu, hv]
  ring

lemma physical_direction (b : Features d) (s : Point (Features d)) (h : Aligned b s) :
    physical (marginGrad (sumFeature b) (diffFeature b) s) =
      LongTails.Setups.TwoSampleQuadraticPerceptron.direction .conv d b (physical s) := by
  obtain ⟨hu, hv⟩ := aligned_parts b s h
  have hc : (Real.sqrt 2)⁻¹ ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  apply Prod.ext
  · apply Prod.ext
    · change (Real.sqrt 2)⁻¹ * (⟪sumFeature b, s.fst.snd⟫ + ⟪diffFeature b, s.snd.snd⟫) =
        ⟪b, s.fst.snd + s.snd.snd⟫
      simp only [sumFeature, diffFeature, real_inner_smul_left, inner_add_left,
        inner_sub_left, inner_add_right, hu, hv]
      linear_combination (2 * ⟪b,s.fst.snd⟫ + 2 * ⟪b,s.snd.snd⟫) * hc
    · change (Real.sqrt 2)⁻¹ * (⟪sumFeature b, s.fst.snd⟫ - ⟪diffFeature b, s.snd.snd⟫) =
        ⟪shift b, s.fst.snd + s.snd.snd⟫
      simp only [sumFeature, diffFeature, real_inner_smul_left, inner_add_left,
        inner_sub_left, inner_add_right, hu, hv]
      linear_combination (2 * ⟪b,s.fst.snd⟫ - 2 * ⟪b,s.snd.snd⟫) * hc
  · change s.fst.fst • sumFeature b + s.snd.fst • diffFeature b =
      ((Real.sqrt 2)⁻¹ * (s.fst.fst + s.snd.fst)) • b +
      ((Real.sqrt 2)⁻¹ * (s.fst.fst - s.snd.fst)) • shift b
    unfold sumFeature diffFeature
    module

variable {p : Params} (D : Data p)

noncomputable def state (η : ℝ) (k : ℕ) : Point (Features p.d) :=
  path (sumFeature ∘ D) (diffFeature ∘ D) η k

lemma aligned_state (G : Geometry p D) (η : ℝ) (k : ℕ) :
    ∀ i, Aligned (D i) (state D η k) := by
  induction k with
  | zero => intro i; simp [Aligned, state, path, initial]
  | succ k ih =>
    let s := state D η k
    let m := scores (sumFeature ∘ D) (diffFeature ∘ D) s
    have hf (i j) : ⟪diffFeature (D i), sumFeature (D j)⟫ = 0 := by
      rw [real_inner_comm]; exact G.orthogonal j i
    intro i
    obtain ⟨h₁,h₂⟩ := ih i
    change ⟪sumFeature (D i), s.snd.snd⟫ = 0 at h₁
    change ⟪diffFeature (D i), s.fst.snd⟫ = 0 at h₂
    change ⟪sumFeature (D i), s.snd.snd + η • (s.snd.fst • mean m (diffFeature ∘ D))⟫ = 0 ∧
      ⟪diffFeature (D i), s.fst.snd + η • (s.fst.fst • mean m (sumFeature ∘ D))⟫ = 0
    simp [inner_add_right, real_inner_smul_right, mean, inner_sum,
      G.orthogonal, hf, h₁, h₂]

noncomputable def increment (θ : LongTails.Setups.ManySampleConvolutionalPerceptron.Space p.d)
    (i : Fin p.n) := (1 / (1 + Real.exp (answer p D (i, θ)).margin)) •
      (answer p D (i, θ)).direction

lemma physical_update (G : Geometry p D) (η : ℝ) (k : ℕ) :
    physical (state D η (k + 1)) = physical (state D η k) +
      (η / p.n) • ∑ i, increment D (physical (state D η k)) i := by
  let s := state D η k
  change physical (update (sumFeature ∘ D) (diffFeature ∘ D) η s) = _
  rw [update, map_add, map_smul, velocity_eq, BilinearLogisticDescent.direction,
    map_smul, map_sum, smul_smul, ← div_eq_mul_inv]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  change SoftQuadraticDynamics.weight (margin (sumFeature (D i)) (diffFeature (D i)) s) •
    physical (marginGrad (sumFeature (D i)) (diffFeature (D i)) s) = _
  rw [← physical_score _ _ (aligned_state D G η k i),
    physical_direction _ _ (aligned_state D G η k i)]
  rfl

end LongTails.Proofs.CyclicLogisticCoordinates
