import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting

open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticCohypomonotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure OpHyp (F : E → E) (G : E → Set E) (J : ℝ → E → E) (L ρ : ℝ) : Prop where
  res : ∀ γ z, 0 < γ → γ⁻¹ • (z - J γ z) ∈ G (J γ z)
  mono : ∀ x y, ∀ a ∈ G x, ∀ b ∈ G y, 0 ≤ ⟪a - b, x - y⟫
  lip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖
  cohypo : ∀ x y, ∀ a ∈ G x, ∀ b ∈ G y,
    -ρ * ‖(F x + a) - (F y + b)‖ ^ 2 ≤ ⟪(F x + a) - (F y + b), x - y⟫
  L_pos : 0 < L
  ρ_nonneg : 0 ≤ ρ

variable {F : E → E} {G : E → Set E} {J : ℝ → E → E} {L ρ : ℝ}

lemma OpHyp.res_unique (H : OpHyp F G J L ρ) {γ : ℝ} (hγ : 0 < γ) {y p : E}
    (hp : γ⁻¹ • (y - p) ∈ G p) : J γ y = p := by
  have hm := H.mono _ _ _ hp _ (H.res γ y hγ)
  have e : γ⁻¹ • (y - p) - γ⁻¹ • (y - J γ y) = γ⁻¹ • (J γ y - p) := by
    rw [← smul_sub]; congr 1; abel
  rw [e, inner_smul_left] at hm
  have h1 : 0 ≤ ⟪J γ y - p, p - J γ y⟫ := by
    have hg : 0 < γ⁻¹ := inv_pos.mpr hγ
    simp only [conj_trivial] at hm
    exact nonneg_of_mul_nonneg_right (by linarith) hg
  have h2 : ⟪J γ y - p, p - J γ y⟫ = -‖J γ y - p‖ ^ 2 := by
    rw [← neg_sub (J γ y) p, inner_neg_right, real_inner_self_eq_norm_sq]
  rw [h2] at h1
  have : ‖J γ y - p‖ = 0 := by nlinarith [norm_nonneg (J γ y - p)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

lemma OpHyp.res_nonexp (H : OpHyp F G J L ρ) {γ : ℝ} (hγ : 0 < γ) (a b : E) :
    ‖J γ a - J γ b‖ ≤ ‖a - b‖ := by
  have hm := H.mono _ _ _ (H.res γ a hγ) _ (H.res γ b hγ)
  have e : γ⁻¹ • (a - J γ a) - γ⁻¹ • (b - J γ b) = γ⁻¹ • ((a - b) - (J γ a - J γ b)) := by
    rw [← smul_sub]; congr 1; abel
  rw [e, inner_smul_left] at hm
  simp only [conj_trivial] at hm
  have hg : 0 < γ⁻¹ := inv_pos.mpr hγ
  have h1 : 0 ≤ ⟪(a - b) - (J γ a - J γ b), J γ a - J γ b⟫ :=
    nonneg_of_mul_nonneg_right (by linarith) hg
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at h1
  have h2 := real_inner_le_norm (a - b) (J γ a - J γ b)
  by_cases h0 : ‖J γ a - J γ b‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hp : 0 < ‖J γ a - J γ b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

lemma OpHyp.reg_pair (H : OpHyp F G J L ρ) {Λ : ℝ} (c x y a b : E) (ha : a ∈ G x) (hb : b ∈ G y) :
    -ρ * ‖(F x + a + Λ • (x - c)) - (F y + b + Λ • (y - c))‖ ^ 2 +
        Λ * (1 - ρ * Λ) * ‖x - y‖ ^ 2 ≤
      (1 - 2 * ρ * Λ) * ⟪(F x + a + Λ • (x - c)) - (F y + b + Λ • (y - c)), x - y⟫ := by
  have hc := H.cohypo x y a ha b hb
  set w := (F x + a + Λ • (x - c)) - (F y + b + Λ • (y - c))
  have hd : (F x + a) - (F y + b) = w - Λ • (x - y) := by
    simp only [w, smul_sub]; abel
  rw [hd] at hc
  have e1 : ‖w - Λ • (x - y)‖ ^ 2 = ‖w‖ ^ 2 - 2 * Λ * ⟪w, x - y⟫ + Λ ^ 2 * ‖x - y‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
  have e2 : ⟪w - Λ • (x - y), x - y⟫ = ⟪w, x - y⟫ - Λ * ‖x - y‖ ^ 2 := by
    rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq]; simp
  rw [e1, e2] at hc
  nlinarith


section Zero

variable [CompleteSpace E]

omit [CompleteSpace E] in
lemma OpHyp.inner_lip (H : OpHyp F G J L ρ) {γ : ℝ} (hγ : 0 < γ) (hγL : γ * L < 1) (x : E) :
    ContractingWith (Real.toNNReal (γ * L)) (fun y => J γ (x - γ • F y)) := by
  refine ⟨by rw [Real.toNNReal_lt_one]; exact hγL, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by have := H.L_pos; positivity)]
  refine (H.res_nonexp hγ _ _).trans ?_
  have e : (x - γ • F a) - (x - γ • F b) = γ • (F b - F a) := by rw [smul_sub]; abel
  rw [e, norm_smul, Real.norm_of_nonneg hγ.le, mul_assoc]
  gcongr
  rw [norm_sub_rev]; exact H.lip a b

noncomputable def resH (H : OpHyp F G J L ρ) {γ : ℝ} (hγ : 0 < γ) (hγL : γ * L < 1) (x : E) : E :=
  ContractingWith.fixedPoint _ (H.inner_lip hγ hγL x)

lemma OpHyp.resH_eq (H : OpHyp F G J L ρ) {γ : ℝ} (hγ : 0 < γ) (hγL : γ * L < 1) (x : E) :
    J γ (x - γ • F (resH H hγ hγL x)) = resH H hγ hγL x :=
  ContractingWith.fixedPoint_isFixedPt (f := fun y => J γ (x - γ • F y)) (H.inner_lip hγ hγL x)

lemma OpHyp.resH_mem (H : OpHyp F G J L ρ) {γ : ℝ} (hγ : 0 < γ) (hγL : γ * L < 1) (x : E) :
    γ⁻¹ • (x - resH H hγ hγL x) - F (resH H hγ hγL x) ∈ G (resH H hγ hγL x) := by
  have h := H.res γ (x - γ • F (resH H hγ hγL x)) hγ
  rw [H.resH_eq hγ hγL x] at h
  have e : γ⁻¹ • (x - γ • F (resH H hγ hγL x) - resH H hγ hγL x) =
      γ⁻¹ • (x - resH H hγ hγL x) - F (resH H hγ hγL x) := by
    rw [show x - γ • F (resH H hγ hγL x) - resH H hγ hγL x =
      (x - resH H hγ hγL x) - γ • F (resH H hγ hγL x) by abel, smul_sub, smul_smul,
      inv_mul_cancel₀ hγ.ne', one_smul]
  rwa [e] at h

omit [CompleteSpace E] in
lemma norm_le_of_cohypo_scalar {ρ γ : ℝ} (hρ : 0 ≤ ρ) (hγ : 0 < γ) (h2ρ : 2 * ρ ≤ γ) (A B : E)
    (h : -ρ * ‖A - B‖ ^ 2 ≤ γ * ⟪A - B, B⟫) : ‖B‖ ≤ ‖A‖ := by
  have e1 : ‖A - B‖ ^ 2 = ‖A‖ ^ 2 - 2 * ⟪A, B⟫ + ‖B‖ ^ 2 := norm_sub_sq_real A B
  have e2 : ⟪A - B, B⟫ = ⟪A, B⟫ - ‖B‖ ^ 2 := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
  rw [e1, e2] at h
  have hAB := real_inner_le_norm A B
  have hAB' : (γ - 2 * ρ) * ⟪A, B⟫ ≤ (γ - 2 * ρ) * (‖A‖ * ‖B‖) :=
    mul_le_mul_of_nonneg_left hAB (by linarith)
  by_contra hlt
  push Not at hlt
  have hB : 0 < ‖B‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have h1 : 0 < (γ - ρ) * ‖B‖ + ρ * ‖A‖ := by
    have : 0 < γ - ρ := by linarith
    have := norm_nonneg A
    positivity
  have h2 : 0 < ‖B‖ - ‖A‖ := by linarith
  nlinarith [mul_pos h1 h2]

omit [CompleteSpace E] in
lemma OpHyp.res_pair_nonexp (H : OpHyp F G J L ρ) {γ : ℝ} (hγ : 0 < γ) (h2ρ : 2 * ρ ≤ γ)
    {x y p q : E} (hp : γ⁻¹ • (x - p) - F p ∈ G p) (hq : γ⁻¹ • (y - q) - F q ∈ G q) :
    ‖p - q‖ ≤ ‖x - y‖ := by
  have hc := H.cohypo p q _ hp _ hq
  have e1 : F p + (γ⁻¹ • (x - p) - F p) = γ⁻¹ • (x - p) := by abel
  have e2 : F q + (γ⁻¹ • (y - q) - F q) = γ⁻¹ • (y - q) := by abel
  have e3 : (x - p) - (y - q) = (x - y) - (p - q) := by abel
  rw [e1, e2, ← smul_sub, e3, inner_smul_left, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hc
  simp only [conj_trivial] at hc
  apply norm_le_of_cohypo_scalar H.ρ_nonneg hγ h2ρ
  have hγ2 : γ ^ 2 * γ⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hγ.ne', one_pow]
  have hγ1 : γ ^ 2 * γ⁻¹ = γ := by rw [sq, mul_assoc, mul_inv_cancel₀ hγ.ne', mul_one]
  have := mul_le_mul_of_nonneg_left hc (sq_nonneg γ)
  calc -ρ * ‖(x - y) - (p - q)‖ ^ 2 = γ ^ 2 * (-ρ * (γ⁻¹ ^ 2 * ‖(x - y) - (p - q)‖ ^ 2)) := by
        rw [show γ ^ 2 * (-ρ * (γ⁻¹ ^ 2 * ‖(x - y) - (p - q)‖ ^ 2)) =
          (γ ^ 2 * γ⁻¹ ^ 2) * (-ρ * ‖(x - y) - (p - q)‖ ^ 2) by ring, hγ2, one_mul]
    _ ≤ γ ^ 2 * (γ⁻¹ * ⟪(x - y) - (p - q), p - q⟫) := this
    _ = γ * ⟪(x - y) - (p - q), p - q⟫ := by rw [← mul_assoc, hγ1]

lemma OpHyp.resH_nonexp (H : OpHyp F G J L ρ) {γ : ℝ} (hγ : 0 < γ) (hγL : γ * L < 1)
    (h2ρ : 2 * ρ ≤ γ) (x y : E) :
    ‖resH H hγ hγL x - resH H hγ hγL y‖ ≤ ‖x - y‖ :=
  H.res_pair_nonexp hγ h2ρ (H.resH_mem hγ hγL x) (H.resH_mem hγ hγL y)

lemma OpHyp.zero_contract (H : OpHyp F G J L ρ) {γ : ℝ} (hγ : 0 < γ) (hγL : γ * L < 1)
    (h2ρ : 2 * ρ ≤ γ) {Λ : ℝ} (hΛ : 0 < Λ) (hγΛ : γ * Λ < 1) (c : E) :
    ContractingWith (Real.toNNReal (1 - γ * Λ))
      (fun z => resH H hγ hγL ((1 - γ * Λ) • z + (γ * Λ) • c)) := by
  refine ⟨by rw [Real.toNNReal_lt_one]; nlinarith, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by linarith)]
  refine (H.resH_nonexp hγ hγL h2ρ _ _).trans ?_
  have e : ((1 - γ * Λ) • a + (γ * Λ) • c) - ((1 - γ * Λ) • b + (γ * Λ) • c) =
      (1 - γ * Λ) • (a - b) := by rw [smul_sub]; abel
  rw [e, norm_smul, Real.norm_of_nonneg (by linarith)]

noncomputable def regZero (H : OpHyp F G J L ρ) {γ : ℝ} (hγ : 0 < γ) (hγL : γ * L < 1)
    (h2ρ : 2 * ρ ≤ γ) {Λ : ℝ} (hΛ : 0 < Λ) (hγΛ : γ * Λ < 1) (c : E) : E :=
  ContractingWith.fixedPoint _ (H.zero_contract hγ hγL h2ρ hΛ hγΛ c)

lemma OpHyp.regZero_mem (H : OpHyp F G J L ρ) {γ : ℝ} (hγ : 0 < γ) (hγL : γ * L < 1)
    (h2ρ : 2 * ρ ≤ γ) {Λ : ℝ} (hΛ : 0 < Λ) (hγΛ : γ * Λ < 1) (c : E) :
    -(F (regZero H hγ hγL h2ρ hΛ hγΛ c) + Λ • (regZero H hγ hγL h2ρ hΛ hγΛ c - c)) ∈
      G (regZero H hγ hγL h2ρ hΛ hγΛ c) := by
  set z := regZero H hγ hγL h2ρ hΛ hγΛ c
  have hfix : resH H hγ hγL ((1 - γ * Λ) • z + (γ * Λ) • c) = z :=
    ContractingWith.fixedPoint_isFixedPt (f := fun z => resH H hγ hγL ((1 - γ * Λ) • z + (γ * Λ) • c))
      (H.zero_contract hγ hγL h2ρ hΛ hγΛ c)
  have h := H.resH_mem hγ hγL ((1 - γ * Λ) • z + (γ * Λ) • c)
  rw [hfix] at h
  have e : γ⁻¹ • ((1 - γ * Λ) • z + (γ * Λ) • c - z) - F z = -(F z + Λ • (z - c)) := by
    have : (1 - γ * Λ) • z + (γ * Λ) • c - z = (γ * Λ) • (c - z) := by
      rw [sub_smul, one_smul, smul_sub]; abel
    rw [this, smul_smul, ← mul_assoc, inv_mul_cancel₀ hγ.ne', one_mul, smul_sub, smul_sub]
    abel
  rwa [e] at h

lemma OpHyp.regZero_lip (H : OpHyp F G J L ρ) {γ : ℝ} (hγ : 0 < γ) (hγL : γ * L < 1)
    (h2ρ : 2 * ρ ≤ γ) {Λ : ℝ} (hΛ : 0 < Λ) (hγΛ : γ * Λ < 1) (c c' : E) :
    ‖regZero H hγ hγL h2ρ hΛ hγΛ c - regZero H hγ hγL h2ρ hΛ hγΛ c'‖ ≤ ‖c - c'‖ := by
  set z := regZero H hγ hγL h2ρ hΛ hγΛ c
  set z' := regZero H hγ hγL h2ρ hΛ hγΛ c'
  have hz : resH H hγ hγL ((1 - γ * Λ) • z + (γ * Λ) • c) = z :=
    ContractingWith.fixedPoint_isFixedPt (f := fun z => resH H hγ hγL ((1 - γ * Λ) • z + (γ * Λ) • c))
      (H.zero_contract hγ hγL h2ρ hΛ hγΛ c)
  have hz' : resH H hγ hγL ((1 - γ * Λ) • z' + (γ * Λ) • c') = z' :=
    ContractingWith.fixedPoint_isFixedPt (f := fun z => resH H hγ hγL ((1 - γ * Λ) • z + (γ * Λ) • c'))
      (H.zero_contract hγ hγL h2ρ hΛ hγΛ c')
  have h := H.resH_nonexp hγ hγL h2ρ ((1 - γ * Λ) • z + (γ * Λ) • c) ((1 - γ * Λ) • z' + (γ * Λ) • c')
  rw [hz, hz'] at h
  have e : ((1 - γ * Λ) • z + (γ * Λ) • c) - ((1 - γ * Λ) • z' + (γ * Λ) • c') =
      (1 - γ * Λ) • (z - z') + (γ * Λ) • (c - c') := by rw [smul_sub, smul_sub]; abel
  rw [e] at h
  have h2 := norm_add_le ((1 - γ * Λ) • (z - z')) ((γ * Λ) • (c - c'))
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
    Real.norm_of_nonneg (by positivity)] at h2
  have hp : 0 < γ * Λ := by positivity
  nlinarith

lemma OpHyp.regZero_continuous (H : OpHyp F G J L ρ) {γ : ℝ} (hγ : 0 < γ) (hγL : γ * L < 1)
    (h2ρ : 2 * ρ ≤ γ) {Λ : ℝ} (hΛ : 0 < Λ) (hγΛ : γ * Λ < 1) :
    Continuous (regZero H hγ hγL h2ρ hΛ hγΛ) :=
  (LipschitzWith.of_dist_le_mul fun a b => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact H.regZero_lip hγ hγL h2ρ hΛ hγΛ a b).continuous

end Zero


end OracleTemplate.StochasticCohypomonotone
