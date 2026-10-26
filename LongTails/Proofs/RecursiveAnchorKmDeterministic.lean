import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

namespace OracleTemplate.RecursiveAnchorKm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def anchorPoint (T : E → E) (Λ : ℝ) (A : E) : E :=
  Classical.epsilon (fun z => (1 + Λ) • z = T z + A)

lemma exists_anchorPoint [CompleteSpace E] {T : E → E} (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    {Λ : ℝ} (hΛ : 0 < Λ) (A : E) : ∃ z, (1 + Λ) • z = T z + A := by
  have hpos : 0 < 1 + Λ := by linarith
  let q : NNReal := ⟨(1 + Λ)⁻¹, by positivity⟩
  let f : E → E := fun x => (1 + Λ)⁻¹ • (T x + A)
  have hq : q < 1 := by
    rw [← NNReal.coe_lt_coe]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  have hf : ContractingWith q f := by
    refine ⟨hq, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    have h : f x - f y = (1 + Λ)⁻¹ • (T x - T y) := by
      simp only [f]
      rw [← smul_sub]
      congr 1
      abel
    rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    exact mul_le_mul_of_nonneg_left (hT x y) (by positivity)
  refine ⟨ContractingWith.fixedPoint f hf, ?_⟩
  have hz : f (ContractingWith.fixedPoint f hf) = ContractingWith.fixedPoint f hf :=
    ContractingWith.fixedPoint_isFixedPt hf
  conv_lhs => rw [← hz]
  simp only [f]
  rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

lemma anchorPoint_spec [CompleteSpace E] {T : E → E} (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    {Λ : ℝ} (hΛ : 0 < Λ) (A : E) :
    (1 + Λ) • anchorPoint T Λ A = T (anchorPoint T Λ A) + A :=
  Classical.epsilon_spec (exists_anchorPoint hT hΛ A)

lemma expand {T : E → E} (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) {Λ : ℝ} (hΛ : 0 ≤ Λ) (a b : E) :
    Λ * ‖a - b‖ ≤ ‖((1 + Λ) • a - T a) - ((1 + Λ) • b - T b)‖ := by
  have h : ((1 + Λ) • a - T a) - ((1 + Λ) • b - T b) = (1 + Λ) • (a - b) - (T a - T b) := by
    rw [smul_sub]; abel
  rw [h]
  have h1 := norm_sub_norm_le ((1 + Λ) • (a - b)) (T a - T b)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h1
  have h2 := hT a b
  nlinarith

lemma anchorPoint_lipschitz [CompleteSpace E] {T : E → E} (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    {Λ : ℝ} (hΛ : 0 < Λ) (A A' : E) :
    Λ * ‖anchorPoint T Λ A - anchorPoint T Λ A'‖ ≤ ‖A - A'‖ := by
  have h := expand hT hΛ.le (anchorPoint T Λ A) (anchorPoint T Λ A')
  rw [anchorPoint_spec hT hΛ A, anchorPoint_spec hT hΛ A'] at h
  simpa using h

lemma continuous_anchorPoint [CompleteSpace E] {T : E → E} (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    {Λ : ℝ} (hΛ : 0 < Λ) : Continuous (anchorPoint T Λ) := by
  have hl : LipschitzWith ⟨Λ⁻¹, by positivity⟩ (anchorPoint T Λ) := by
    refine LipschitzWith.of_dist_le_mul fun A A' => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have h := anchorPoint_lipschitz hT hΛ A A'
    change ‖anchorPoint T Λ A - anchorPoint T Λ A'‖ ≤ Λ⁻¹ * ‖A - A'‖
    rw [le_inv_mul_iff₀ hΛ]
    exact h
  exact hl.continuous

section Transition

variable [CompleteSpace E] {T : E → E} (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
  {Λ l : ℝ} (hΛ : 0 < Λ) (hl : 0 ≤ l) (A x : E)

include hT hΛ hl in
lemma transition_shift :
    (Λ + l) * ‖anchorPoint T (Λ + l) (A + l • x) - anchorPoint T Λ A‖ ≤
      l * ‖x - anchorPoint T Λ A‖ := by
  have hΛ' : 0 < Λ + l := by linarith
  set z := anchorPoint T Λ A
  set z' := anchorPoint T (Λ + l) (A + l • x)
  have h := expand hT hΛ'.le z' z
  have hz := anchorPoint_spec hT hΛ A
  have hz' := anchorPoint_spec hT hΛ' (A + l • x)
  have he : ((1 + (Λ + l)) • z' - T z') - ((1 + (Λ + l)) • z - T z) = l • (x - z) := by
    rw [hz', show (1 + (Λ + l)) • z = (1 + Λ) • z + l • z by rw [← add_smul]; ring_nf, hz,
      smul_sub]
    abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl] at h
  exact h

include hT hΛ hl in
lemma transition_move :
    ‖anchorPoint T (Λ + l) (A + l • x) - anchorPoint T Λ A‖ ≤ ‖x - anchorPoint T Λ A‖ := by
  have h := transition_shift hT hΛ hl A x
  have hΛ' : 0 < Λ + l := by linarith
  have h1 : l * ‖x - anchorPoint T Λ A‖ ≤ (Λ + l) * ‖x - anchorPoint T Λ A‖ :=
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have h2 := le_trans h h1
  exact le_of_mul_le_mul_left h2 hΛ'

include hT hΛ hl in
lemma transition_start :
    ‖x - anchorPoint T (Λ + l) (A + l • x)‖ ≤ 2 * ‖x - anchorPoint T Λ A‖ := by
  have h := transition_move hT hΛ hl A x
  have h1 := norm_sub_le (x - anchorPoint T Λ A)
    (anchorPoint T (Λ + l) (A + l • x) - anchorPoint T Λ A)
  rw [show x - anchorPoint T Λ A - (anchorPoint T (Λ + l) (A + l • x) - anchorPoint T Λ A) =
    x - anchorPoint T (Λ + l) (A + l • x) by abel] at h1
  linarith

include hT hΛ hl in
lemma transition_gap :
    ‖(A + l • x) - (Λ + l) • anchorPoint T (Λ + l) (A + l • x)‖ ≤
      ‖A - Λ • anchorPoint T Λ A‖ + 3 * l * ‖x - anchorPoint T Λ A‖ := by
  set z := anchorPoint T Λ A
  set z' := anchorPoint T (Λ + l) (A + l • x)
  have he : (A + l • x) - (Λ + l) • z' = (A - Λ • z) + Λ • (z - z') + l • (x - z') := by
    rw [add_smul, smul_sub, smul_sub]; abel
  rw [he]
  have h1 := norm_add₃_le (a := A - Λ • z) (b := Λ • (z - z')) (c := l • (x - z'))
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hΛ,
    abs_of_nonneg hl, norm_sub_rev z z'] at h1
  have h2 := transition_shift hT hΛ hl A x
  have h3 := transition_start hT hΛ hl A x
  have h4 : Λ * ‖z' - z‖ ≤ (Λ + l) * ‖z' - z‖ :=
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have h5 : l * ‖x - z'‖ ≤ l * (2 * ‖x - z‖) := mul_le_mul_of_nonneg_left h3 hl
  nlinarith

end Transition

lemma residual_le [CompleteSpace E] {T : E → E} (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    {Λ : ℝ} (hΛ : 0 < Λ) (A x : E) :
    ‖x - T x‖ ≤ 2 * ‖x - anchorPoint T Λ A‖ + ‖A - Λ • anchorPoint T Λ A‖ := by
  set z := anchorPoint T Λ A
  have hz := anchorPoint_spec hT hΛ A
  have hzz : z - T z = A - Λ • z := by
    have : (1 + Λ) • z = z + Λ • z := by rw [add_smul, one_smul]
    rw [this] at hz
    rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'.mpr hz.symm]
    abel
  have he : x - T x = (x - z) + (z - T z) + (T z - T x) := by abel
  rw [he]
  have h1 := norm_add₃_le (a := x - z) (b := z - T z) (c := T z - T x)
  have h2 := hT z x
  rw [norm_sub_rev z x] at h2
  rw [hzz] at h1 ⊢
  linarith

lemma initial_le [CompleteSpace E] {T : E → E} (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    {l : ℝ} (hl : 0 < l) (x0 xstar : E) (hstar : T xstar = xstar) :
    ‖x0 - anchorPoint T l (l • x0)‖ ≤ 2 * ‖x0 - xstar‖ := by
  set z := anchorPoint T l (l • x0)
  have hz := anchorPoint_spec hT hl (l • x0)
  have he : (1 + l) • (z - xstar) = (T z - T xstar) + l • (x0 - xstar) := by
    rw [smul_sub, hz, hstar, smul_sub, add_smul, one_smul]; abel
  have h1 := congrArg norm he
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)] at h1
  have h2 := norm_add_le (T z - T xstar) (l • (x0 - xstar))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl] at h2
  have h3 := hT z xstar
  have h4 : ‖z - xstar‖ ≤ ‖x0 - xstar‖ := by nlinarith
  have h5 := norm_sub_le (x0 - xstar) (z - xstar)
  rw [show x0 - xstar - (z - xstar) = x0 - z by abel] at h5
  linarith

end OracleTemplate.RecursiveAnchorKm
