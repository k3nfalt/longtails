import Mathlib.Analysis.InnerProductSpace.Basic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoSidedPerceptronDynamics

@[ext] structure State (E : Type*) where
  a : ℝ
  q : ℝ
  t : ℝ
  z : E

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def feature (p r : E) (x : State E) : E := x.a • p + x.t • r

noncomputable def step (c δ : ℝ) (p r : E) (x : State E) : State E :=
  ⟨x.a + c * x.q + δ * ⟪p, x.z⟫, x.q + c * x.a, x.t + δ * ⟪r, x.z⟫, x.z + δ • feature p r x⟩

noncomputable def margin (c δ : ℝ) (p r : E) (x : State E) : ℝ :=
  c * x.a * x.q + δ * ⟪feature p r x, x.z⟫

def mass (x : State E) : ℝ := |x.a + x.q| + |x.a - x.q|

def gap (x : State E) : ℝ := |x.a + x.q| - |x.a - x.q|

noncomputable def potential (C : ℝ) (x : State E) : ℝ := ‖x.z‖ ^ 2 + (mass x) ^ 2 / (4 - 4 * C)

lemma feature_inner (p r : E) (x : State E) :
    ⟪feature p r x, x.z⟫ = x.a * ⟪p, x.z⟫ + x.t * ⟪r, x.z⟫ := by
  simp [feature, inner_add_left, real_inner_smul_left]

lemma feature_inner_right (p r w : E) (x : State E) :
    ⟪feature p r x, w⟫ = x.a * ⟪p, w⟫ + x.t * ⟪r, w⟫ := by
  simp [feature, inner_add_left, real_inner_smul_left]

lemma feature_norm_le {p r : E} (hp : ‖p‖ ≤ 1) (hr : ‖r‖ ≤ 1) (x : State E) :
    ‖feature p r x‖ ≤ |x.a| + |x.t| := by
  calc
    _ ≤ ‖x.a • p‖ + ‖x.t • r‖ := norm_add_le _ _
    _ = |x.a| * ‖p‖ + |x.t| * ‖r‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ _ := by nlinarith [abs_nonneg x.a, abs_nonneg x.t]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma mass_nonneg (x : State E) : 0 ≤ mass x := add_nonneg (abs_nonneg _) (abs_nonneg _)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma abs_gap_le_mass (x : State E) : |gap x| ≤ mass x := by
  unfold gap mass
  rw [abs_le]
  constructor <;> linarith [abs_nonneg (x.a + x.q), abs_nonneg (x.a - x.q)]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma gap_mul_mass (x : State E) : gap x * mass x = 4 * (x.a * x.q) := by
  unfold gap mass
  have h1 : |x.a + x.q| ^ 2 = (x.a + x.q) ^ 2 := sq_abs _
  have h2 : |x.a - x.q| ^ 2 = (x.a - x.q) ^ 2 := sq_abs _
  linear_combination h1 - h2

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma two_abs_a_le_mass (x : State E) : 2 * |x.a| ≤ mass x := by
  unfold mass
  have : 2 * x.a = (x.a + x.q) + (x.a - x.q) := by ring
  calc
    2 * |x.a| = |2 * x.a| := by rw [abs_mul]; norm_num
    _ = |(x.a + x.q) + (x.a - x.q)| := by rw [this]
    _ ≤ _ := abs_add_le _ _

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma two_abs_q_le_mass (x : State E) : 2 * |x.q| ≤ mass x := by
  unfold mass
  have : 2 * x.q = (x.a + x.q) - (x.a - x.q) := by ring
  calc
    2 * |x.q| = |2 * x.q| := by rw [abs_mul]; norm_num
    _ = |(x.a + x.q) - (x.a - x.q)| := by rw [this]
    _ ≤ _ := abs_sub _ _

omit [InnerProductSpace ℝ E] in
lemma sq_mass_le_potential {C : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ 1 / 2) (x : State E) :
    (mass x) ^ 2 ≤ 4 * potential C x := by
  unfold potential
  have h4 : 2 ≤ 4 - 4 * C := by linarith
  have hm := sq_nonneg (mass x)
  have hz := sq_nonneg ‖x.z‖
  have : (mass x) ^ 2 / 4 ≤ (mass x) ^ 2 / (4 - 4 * C) := by
    apply div_le_div_of_nonneg_left hm (by linarith) (by linarith)
  linarith

omit [InnerProductSpace ℝ E] in
lemma norm_z_sq_le_potential {C : ℝ} (hC : C ≤ 1 / 2) (x : State E) :
    ‖x.z‖ ^ 2 ≤ potential C x := by
  unfold potential
  have h4 : 0 < 4 - 4 * C := by linarith
  have := div_nonneg (sq_nonneg (mass x)) h4.le
  linarith

omit [InnerProductSpace ℝ E] in
lemma potential_nonneg {C : ℝ} (hC : C ≤ 1 / 2) (x : State E) : 0 ≤ potential C x :=
  (sq_nonneg _).trans (norm_z_sq_le_potential hC x)

section Step

variable {c δ : ℝ} {p r : E} {x : State E}

lemma step_a : (step c δ p r x).a = x.a + c * x.q + δ * ⟪p, x.z⟫ := rfl
lemma step_q : (step c δ p r x).q = x.q + c * x.a := rfl
lemma step_t : (step c δ p r x).t = x.t + δ * ⟪r, x.z⟫ := rfl
lemma step_z : (step c δ p r x).z = x.z + δ • feature p r x := rfl

lemma step_z_norm_sq :
    ‖(step c δ p r x).z‖ ^ 2 =
      ‖x.z‖ ^ 2 + 2 * δ * ⟪feature p r x, x.z⟫ + δ ^ 2 * ‖feature p r x‖ ^ 2 := by
  rw [step_z, norm_add_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs, mul_pow,
    sq_abs, real_inner_comm]
  ring

lemma step_z_norm_le (hδ : 0 ≤ δ) :
    ‖(step c δ p r x).z‖ ≤ ‖x.z‖ + δ * ‖feature p r x‖ := by
  rw [step_z]
  calc
    _ ≤ ‖x.z‖ + ‖δ • feature p r x‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ]

lemma step_t_sub_le (hδ : 0 ≤ δ) (hr : ‖r‖ ≤ 1) :
    |(step c δ p r x).t - x.t| ≤ δ * ‖x.z‖ := by
  rw [step_t]
  have h := abs_real_inner_le_norm r x.z
  simp only [add_sub_cancel_left, abs_mul, abs_of_nonneg hδ]
  calc
    δ * |⟪r, x.z⟫| ≤ δ * (‖r‖ * ‖x.z‖) := by gcongr
    _ ≤ δ * (1 * ‖x.z‖) := by gcongr
    _ = δ * ‖x.z‖ := by ring

lemma step_sum : (step c δ p r x).a + (step c δ p r x).q =
    (1 + c) * (x.a + x.q) + δ * ⟪p, x.z⟫ := by
  simp only [step_a, step_q]; ring

lemma step_diff : (step c δ p r x).a - (step c δ p r x).q =
    (1 - c) * (x.a - x.q) + δ * ⟪p, x.z⟫ := by
  simp only [step_a, step_q]; ring

lemma mass_step_le (hc : |c| ≤ 1) :
    mass (step c δ p r x) ≤ mass x + c * gap x + 2 * |δ * ⟪p, x.z⟫| := by
  unfold mass gap
  rw [step_sum, step_diff]
  have h1 : |(1 + c) * (x.a + x.q) + δ * ⟪p, x.z⟫| ≤
      (1 + c) * |x.a + x.q| + |δ * ⟪p, x.z⟫| := by
    calc
      _ ≤ |(1 + c) * (x.a + x.q)| + |δ * ⟪p, x.z⟫| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_of_nonneg (by linarith [abs_le.mp hc])]
  have h2 : |(1 - c) * (x.a - x.q) + δ * ⟪p, x.z⟫| ≤
      (1 - c) * |x.a - x.q| + |δ * ⟪p, x.z⟫| := by
    calc
      _ ≤ |(1 - c) * (x.a - x.q)| + |δ * ⟪p, x.z⟫| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_of_nonneg (by linarith [abs_le.mp hc])]
  linarith [h1, h2]

lemma gap_step_ge_of_nonneg (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    gap x + c * mass x - 2 * |δ * ⟪p, x.z⟫| ≤ gap (step c δ p r x) := by
  unfold gap mass
  rw [step_sum, step_diff]
  have h1 : (1 + c) * |x.a + x.q| - |δ * ⟪p, x.z⟫| ≤
      |(1 + c) * (x.a + x.q) + δ * ⟪p, x.z⟫| := by
    have := abs_sub ((1 + c) * (x.a + x.q) + δ * ⟪p, x.z⟫) (δ * ⟪p, x.z⟫)
    rw [add_sub_cancel_right, abs_mul (1 + c), abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + c)] at this
    linarith
  have h2 : |(1 - c) * (x.a - x.q) + δ * ⟪p, x.z⟫| ≤
      (1 - c) * |x.a - x.q| + |δ * ⟪p, x.z⟫| := by
    calc
      _ ≤ |(1 - c) * (x.a - x.q)| + |δ * ⟪p, x.z⟫| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_of_nonneg (by linarith)]
  linarith [h1, h2]

lemma gap_step_le_of_nonpos (hc : c ≤ 0) (hc1 : -1 ≤ c) :
    gap (step c δ p r x) ≤ gap x + c * mass x + 2 * |δ * ⟪p, x.z⟫| := by
  unfold gap mass
  rw [step_sum, step_diff]
  have h1 : |(1 + c) * (x.a + x.q) + δ * ⟪p, x.z⟫| ≤
      (1 + c) * |x.a + x.q| + |δ * ⟪p, x.z⟫| := by
    calc
      _ ≤ |(1 + c) * (x.a + x.q)| + |δ * ⟪p, x.z⟫| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_of_nonneg (by linarith)]
  have h2 : (1 - c) * |x.a - x.q| - |δ * ⟪p, x.z⟫| ≤
      |(1 - c) * (x.a - x.q) + δ * ⟪p, x.z⟫| := by
    have := abs_sub ((1 - c) * (x.a - x.q) + δ * ⟪p, x.z⟫) (δ * ⟪p, x.z⟫)
    rw [add_sub_cancel_right, abs_mul (1 - c), abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - c)] at this
    linarith
  linarith [h1, h2]

lemma mass_sq_step_le {C : ℝ} (hcC : |c| ≤ C) (hC : C ≤ 1) :
    (mass (step c δ p r x)) ^ 2 ≤
      (mass x) ^ 2 + 8 * (c * x.a * x.q) + 4 * C * |c * x.a * x.q| +
        4 * (1 + C) * mass x * |δ * ⟪p, x.z⟫| + 4 * |δ * ⟪p, x.z⟫| ^ 2 := by
  have hc1 : |c| ≤ 1 := hcC.trans hC
  set φ := |δ * ⟪p, x.z⟫| with hφ
  set M := mass x with hM
  set G := c * gap x with hG
  have hφ0 : 0 ≤ φ := abs_nonneg _
  have hM0 : 0 ≤ M := mass_nonneg x
  have hgm := abs_gap_le_mass x
  have hC0 : 0 ≤ C := (abs_nonneg c).trans hcC
  have hGM : |G| ≤ C * M := by
    rw [hG, abs_mul]
    exact mul_le_mul hcC hgm (abs_nonneg _) hC0
  have hG1 : |G| ≤ M := by
    have : C * M ≤ M := by nlinarith
    linarith
  have hstep : mass (step c δ p r x) ≤ M + G + 2 * φ := mass_step_le hc1
  have hB : 0 ≤ M + G + 2 * φ := by linarith [neg_abs_le G]
  have hsq : (mass (step c δ p r x)) ^ 2 ≤ (M + G + 2 * φ) ^ 2 :=
    pow_le_pow_left₀ (mass_nonneg _) hstep 2
  have hcaq : c * x.a * x.q = G * M / 4 := by
    rw [hG, hM, mul_assoc c (gap x), gap_mul_mass]; ring
  have habs : |c * x.a * x.q| = |G| * M / 4 := by
    rw [hcaq, abs_div, abs_mul, abs_of_nonneg hM0]; norm_num
  have hGG : G ^ 2 ≤ C * |G| * M := by
    have e1 : G ^ 2 = |G| * |G| := by rw [← sq_abs]; ring
    rw [e1]
    calc
      |G| * |G| ≤ |G| * (C * M) := mul_le_mul_of_nonneg_left hGM (abs_nonneg G)
      _ = C * |G| * M := by ring
  have hGφ : G * φ ≤ C * M * φ := by
    have := le_abs_self G
    nlinarith
  have hexp : (M + G + 2 * φ) ^ 2 =
      M ^ 2 + 2 * M * G + G ^ 2 + 4 * φ * M + 4 * (G * φ) + 4 * φ ^ 2 := by ring
  rw [hexp] at hsq
  have habs' : |G * M / 4| = |G| * M / 4 := by
    rw [abs_div, abs_mul, abs_of_nonneg hM0]; norm_num
  rw [hcaq, habs']
  nlinarith [hGG, hGφ, hφ0, hM0]

lemma mass_step_ge (hc : |c| ≤ 1) :
    mass x + c * gap x - 2 * |δ * ⟪p, x.z⟫| ≤ mass (step c δ p r x) := by
  unfold mass gap
  rw [step_sum, step_diff]
  have hc' := abs_le.mp hc
  have h1 : (1 + c) * |x.a + x.q| - |δ * ⟪p, x.z⟫| ≤
      |(1 + c) * (x.a + x.q) + δ * ⟪p, x.z⟫| := by
    have := abs_sub ((1 + c) * (x.a + x.q) + δ * ⟪p, x.z⟫) (δ * ⟪p, x.z⟫)
    rw [add_sub_cancel_right, abs_mul (1 + c), abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + c)] at this
    linarith
  have h2 : (1 - c) * |x.a - x.q| - |δ * ⟪p, x.z⟫| ≤
      |(1 - c) * (x.a - x.q) + δ * ⟪p, x.z⟫| := by
    have := abs_sub ((1 - c) * (x.a - x.q) + δ * ⟪p, x.z⟫) (δ * ⟪p, x.z⟫)
    rw [add_sub_cancel_right, abs_mul (1 - c), abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - c)] at this
    linarith
  linarith [h1, h2]

end Step

end LongTails.Proofs.TwoSidedPerceptronDynamics
