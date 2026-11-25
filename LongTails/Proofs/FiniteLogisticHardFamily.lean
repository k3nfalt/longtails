import LongTails.Proofs.FiniteLogisticLinearComparison
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped RealInnerProductSpace

namespace LongTails.Proofs.FiniteLogisticHardFamily

open FiniteLogisticLinearComparison SoftQuadraticDynamics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def data (z u v : E) (μ : ℝ) : Fin 6 → E :=
  ![z + μ • v, z + μ • v, -z + μ • v, (1 / 128 : ℝ) • u + μ • v,
    (1 / 128 : ℝ) • u + μ • v, (-1 / 128 : ℝ) • u + μ • v]

noncomputable def linearStep {n : ℕ} (D : Fin n → E) (η : ℝ) (w : E) : E :=
  w + (η / n) • ∑ i, weight ⟪D i, w⟫ • D i

noncomputable def linearPath {n : ℕ} (D : Fin n → E) (η : ℝ) : ℕ → E
  | 0 => 0
  | k + 1 => linearStep D η (linearPath D η k)

noncomputable def scores (z u v : E) (μ : ℝ) (w : E) : Scores :=
  ⟨⟪z, w⟫, μ * ⟪v, w⟫, (1 / 128 : ℝ) * ⟪u, w⟫⟩

private lemma step_scores (z u v : E) (μ η : ℝ)
    (hz : ⟪z, z⟫ = 1) (hu : ⟪u, u⟫ = 1) (hv : ⟪v, v⟫ = 1)
    (hzu : ⟪z, u⟫ = 0) (hzv : ⟪z, v⟫ = 0) (huv : ⟪u, v⟫ = 0)
    (w : E) :
    scores z u v μ (linearStep (data z u v μ) η w) =
      step (η / 6) μ (scores z u v μ w) := by
  have huz : ⟪u, z⟫ = 0 := (real_inner_comm ..).trans hzu
  have hvz : ⟪v, z⟫ = 0 := (real_inner_comm ..).trans hzv
  have hvu : ⟪v, u⟫ = 0 := (real_inner_comm ..).trans huv
  rw [real_inner_self_eq_norm_sq] at hz hu hv
  unfold linearStep
  simp [Fin.sum_univ_succ, data, scores, step, mass, inner_add_left, inner_add_right,
    inner_neg_left, inner_neg_right, real_inner_smul_left,
    real_inner_smul_right, hz, hu, hv, hzu, hzv, huv, huz, hvz, hvu]
  refine ⟨?_, ?_, ?_⟩ <;> ring_nf

lemma path_scores (z u v : E) (μ η : ℝ)
    (hz : ⟪z, z⟫ = 1) (hu : ⟪u, u⟫ = 1) (hv : ⟪v, v⟫ = 1)
    (hzu : ⟪z, u⟫ = 0) (hzv : ⟪z, v⟫ = 0) (huv : ⟪u, v⟫ = 0) (k : ℕ) :
    scores z u v μ (linearPath (data z u v μ) η k) = path (η / 6) μ k := by
  induction k with
  | zero => simp [scores, linearPath, path]
  | succ k ih =>
    rw [linearPath, step_scores z u v μ η hz hu hv hzu hzv huv, ih, path]

lemma fails_to_separate (z u v : E) {μ η : ℝ} (hη : 0 < η)
    (hz : ⟪z, z⟫ = 1) (hu : ⟪u, u⟫ = 1) (hv : ⟪v, v⟫ = 1)
    (hzu : ⟪z, u⟫ = 0) (hzv : ⟪z, v⟫ = 0) (huv : ⟪u, v⟫ = 0) (k : ℕ)
    (hk : 1048576 * k * μ ^ 2 ≤ 1) :
    ¬∀ i, 0 < ⟪data z u v μ i, linearPath (data z u v μ) η k⟫ := by
  intro h
  apply uniform_failure (h := η / 6) (by positivity) k hk
  rw [← path_scores z u v μ η hz hu hv hzu hzv huv k]
  generalize linearPath (data z u v μ) η k = w at h ⊢
  have h₀ := h 0
  have h₂ := h 2
  have h₃ := h 3
  have h₅ := h 5
  simp [data, inner_add_left, inner_neg_left, real_inner_smul_left] at h₀ h₂ h₃ h₅
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [scores] <;> linarith only [h₀, h₂, h₃, h₅]

lemma scaled_path {n : ℕ} (D : Fin n → E) (η c : ℝ) (k : ℕ) :
    c • linearPath (fun i => c • D i) η k = linearPath D (η * c ^ 2) k := by
  induction k with
  | zero => simp [linearPath]
  | succ k ih =>
    rw [linearPath, linearPath, linearStep, linearStep, ← ih, smul_add]
    congr 1
    simp only [real_inner_smul_left, real_inner_smul_right]
    simp_rw [smul_comm _ c (D _)]
    rw [← Finset.smul_sum, smul_smul, smul_smul]
    congr 1
    ring

end LongTails.Proofs.FiniteLogisticHardFamily
