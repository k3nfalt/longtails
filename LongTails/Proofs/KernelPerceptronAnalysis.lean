import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.unusedSectionVars false

open scoped RealInnerProductSpace

namespace LongTails.Proofs.KernelPerceptronDynamics

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

@[ext] structure State (F E : Type*) where
  a : ℝ
  q : ℝ
  t : F
  z : E

noncomputable def step (b δ : ℝ) (p : E) (R : F →L[ℝ] E) (x : State F E) : State F E :=
  ⟨x.a + b * x.q + δ * ⟪p, x.z⟫, x.q + b * x.a,
    x.t + δ • (ContinuousLinearMap.adjoint R) x.z, x.z + x.a • p + R x.t⟩

noncomputable def start (a₀ : ℝ) (t₀ : F) : State F E := ⟨a₀, 0, t₀, 0⟩

noncomputable def res (p : E) (R : F →L[ℝ] E) (x : State F E) : ℝ :=
  x.a * ⟪p, x.z⟫ + ⟪R x.t, x.z⟫

def misclassified (b δ : ℝ) (p : E) (R : F →L[ℝ] E) (x : State F E) : Prop :=
  b * x.a * x.q + δ * res p R x ≤ 0

structure Trajectory {ι : Type*} (b : ι → ℝ) (δ : ℝ) (p : ι → E) (R : ι → F →L[ℝ] E)
    (a₀ : ℝ) (t₀ : F) (x : ℕ → State F E) (i : ℕ → ι) (K : ℕ) : Prop where
  initial : x 0 = start a₀ t₀
  update : ∀ k, k < K → x (k + 1) = step (b (i k)) δ (p (i k)) (R (i k)) (x k)
  mistake : ∀ k, k < K → misclassified (b (i k)) δ (p (i k)) (R (i k)) (x k)

noncomputable def phi (x : State F E) : ℝ := |x.a ^ 2 - x.q ^ 2|
noncomputable def mass (x : State F E) : ℝ := x.a ^ 2 + x.q ^ 2
noncomputable def bias (x : State F E) : ℝ := x.a * x.q
noncomputable def noise (δ : ℝ) (p : E) (x : State F E) : ℝ := δ * ⟪p, x.z⟫
noncomputable def move (p : E) (R : F →L[ℝ] E) (x : State F E) : E := x.a • p + R x.t

section OneStep

variable (b δ : ℝ) (p : E) (R : F →L[ℝ] E) (x : State F E)

lemma step_a : (step b δ p R x).a = x.a + b * x.q + noise δ p x := rfl
lemma step_q : (step b δ p R x).q = x.q + b * x.a := rfl
lemma step_t : (step b δ p R x).t = x.t + δ • (ContinuousLinearMap.adjoint R) x.z := rfl
lemma step_z : (step b δ p R x).z = x.z + move p R x := by
  simp only [step, move]; abel

lemma step_sum : (step b δ p R x).a + (step b δ p R x).q =
    (1 + b) * (x.a + x.q) + noise δ p x := by
  simp only [step_a, step_q]; ring

lemma step_diff : (step b δ p R x).a - (step b δ p R x).q =
    (1 - b) * (x.a - x.q) + noise δ p x := by
  simp only [step_a, step_q]; ring

lemma step_mass : mass (step b δ p R x) = mass x + 4 * b * bias x + b ^ 2 * mass x +
    (2 * noise δ p x * (x.a + b * x.q) + noise δ p x ^ 2) := by
  simp only [mass, bias, step_a, step_q]; ring

lemma step_phi_eq : (step b δ p R x).a ^ 2 - (step b δ p R x).q ^ 2 =
    (1 - b ^ 2) * (x.a ^ 2 - x.q ^ 2) +
      noise δ p x * ((1 + b) * (x.a + x.q) + (1 - b) * (x.a - x.q)) + noise δ p x ^ 2 := by
  simp only [step_a, step_q]; ring

lemma step_phi_le (hb : b ^ 2 ≤ 1) : phi (step b δ p R x) ≤ (1 - b ^ 2) * phi x +
    |noise δ p x| * (|(1 + b) * (x.a + x.q)| + |(1 - b) * (x.a - x.q)|) + noise δ p x ^ 2 := by
  unfold phi
  rw [step_phi_eq]
  refine (abs_add_three _ _ _).trans ?_
  have h1 : |noise δ p x * ((1 + b) * (x.a + x.q) + (1 - b) * (x.a - x.q))| ≤
      |noise δ p x| * (|(1 + b) * (x.a + x.q)| + |(1 - b) * (x.a - x.q)|) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
  have h2 : |noise δ p x ^ 2| = noise δ p x ^ 2 := abs_of_nonneg (sq_nonneg _)
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - b ^ 2)]
  linarith

omit [CompleteSpace E] [CompleteSpace F] in
lemma res_eq_inner : res p R x = ⟪x.z, move p R x⟫ := by
  simp only [res, move, inner_add_right, real_inner_smul_right]
  rw [real_inner_comm x.z p, real_inner_comm x.z (R x.t)]

lemma step_z_norm_sq : ‖(step b δ p R x).z‖ ^ 2 =
    ‖x.z‖ ^ 2 + 2 * res p R x + ‖move p R x‖ ^ 2 := by
  rw [step_z, norm_add_sq_real, res_eq_inner]

lemma step_z_inner (w : E) : ⟪w, (step b δ p R x).z⟫ =
    ⟪w, x.z⟫ + x.a * ⟪w, p⟫ + ⟪w, R x.t⟫ := by
  rw [step_z]
  simp only [move, inner_add_right, real_inner_smul_right]
  ring

omit [CompleteSpace E] [CompleteSpace F] in
lemma move_norm_le (hp : ‖p‖ ≤ 1) (hR : ‖R‖ ≤ 1) : ‖move p R x‖ ≤ |x.a| + ‖x.t‖ := by
  unfold move
  calc ‖x.a • p + R x.t‖ ≤ ‖x.a • p‖ + ‖R x.t‖ := norm_add_le _ _
    _ = |x.a| * ‖p‖ + ‖R x.t‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |x.a| * 1 + ‖R‖ * ‖x.t‖ := by
        gcongr
        exact R.le_opNorm x.t
    _ ≤ |x.a| * 1 + 1 * ‖x.t‖ := by gcongr
    _ = |x.a| + ‖x.t‖ := by ring

omit [CompleteSpace E] [CompleteSpace F] in
lemma delta_res_le (h : misclassified b δ p R x) : δ * res p R x ≤ -(b * bias x) := by
  unfold misclassified at h
  unfold bias
  linarith

omit [CompleteSpace E] [CompleteSpace F] in
lemma res_abs_le (hp : ‖p‖ ≤ 1) (hR : ‖R‖ ≤ 1) :
    |res p R x| ≤ (|x.a| + ‖x.t‖) * ‖x.z‖ := by
  rw [res_eq_inner]
  calc |⟪x.z, move p R x⟫| ≤ ‖x.z‖ * ‖move p R x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x.z‖ * (|x.a| + ‖x.t‖) := by gcongr; exact move_norm_le p R x hp hR
    _ = _ := by ring

lemma t_step_norm (hR : ‖R‖ ≤ 1) (hδ : 0 ≤ δ) :
    ‖(step b δ p R x).t - x.t‖ ≤ δ * ‖x.z‖ := by
  rw [step_t, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ]
  apply mul_le_mul_of_nonneg_left _ hδ
  calc ‖(ContinuousLinearMap.adjoint R) x.z‖ ≤ ‖ContinuousLinearMap.adjoint R‖ * ‖x.z‖ :=
        (ContinuousLinearMap.adjoint R).le_opNorm x.z
    _ = ‖R‖ * ‖x.z‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ 1 * ‖x.z‖ := by gcongr
    _ = ‖x.z‖ := one_mul _

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma mass_le_phi_add (x : State F E) : mass x ≤ phi x + 2 * |bias x| := by
  unfold mass phi bias
  rcases le_or_gt 0 (x.a ^ 2 - x.q ^ 2) with h | h
  · rw [abs_of_nonneg h]
    nlinarith [abs_nonneg (x.a * x.q), neg_abs_le (x.a * x.q), sq_nonneg (x.a - x.q),
      sq_nonneg (x.a + x.q), le_abs_self (x.a * x.q)]
  · rw [abs_of_neg h]
    nlinarith [abs_nonneg (x.a * x.q), neg_abs_le (x.a * x.q), sq_nonneg (x.a - x.q),
      sq_nonneg (x.a + x.q), le_abs_self (x.a * x.q)]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma phi_le_mass (x : State F E) : phi x ≤ mass x := by
  unfold phi mass
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg x.a, sq_nonneg x.q]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma abs_a_le_sqrt_mass (x : State F E) : |x.a| ≤ Real.sqrt (mass x) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by unfold mass; nlinarith [sq_nonneg x.q])

omit [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma noise_abs_le (hp : ‖p‖ ≤ 1) (hδ : 0 ≤ δ) : |noise δ p x| ≤ δ * ‖x.z‖ := by
  unfold noise
  rw [abs_mul, abs_of_nonneg hδ]
  apply mul_le_mul_of_nonneg_left _ hδ
  calc |⟪p, x.z⟫| ≤ ‖p‖ * ‖x.z‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * ‖x.z‖ := by gcongr
    _ = ‖x.z‖ := one_mul _

omit [CompleteSpace E] [CompleteSpace F] in
lemma inner_R_shift (w : E) (t₀ : F) (hw : ‖w‖ = 1) (hR : ‖R‖ ≤ 1) :
    ⟪w, R t₀⟫ - ‖x.t - t₀‖ ≤ ⟪w, R x.t⟫ := by
  have h : ⟪w, R x.t⟫ = ⟪w, R t₀⟫ + ⟪w, R (x.t - t₀)⟫ := by
    rw [← inner_add_right, ← map_add, add_sub_cancel]
  rw [h]
  have h2 : |⟪w, R (x.t - t₀)⟫| ≤ ‖x.t - t₀‖ := by
    calc |⟪w, R (x.t - t₀)⟫| ≤ ‖w‖ * ‖R (x.t - t₀)‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * (‖R‖ * ‖x.t - t₀‖) := by
          rw [hw]
          gcongr
          exact R.le_opNorm _
      _ ≤ 1 * (1 * ‖x.t - t₀‖) := by gcongr
      _ = ‖x.t - t₀‖ := by ring
  linarith [neg_abs_le ⟪w, R (x.t - t₀)⟫]

end OneStep

end LongTails.Proofs.KernelPerceptronDynamics


namespace LongTails.Proofs.KernelPerceptronPhaseOne

open KernelPerceptronDynamics

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

structure Control where
  ρ : ℝ
  β : ℝ
  ε : ℝ
  U : ℝ
  φ : ℝ
  rho_pos : 0 < ρ
  rho_le : ρ ≤ β
  beta_le : β ≤ 1 / 8
  eps_nonneg : 0 ≤ ε
  U_ge : 1 ≤ U
  phi_pos : 0 < φ
  phi_le : φ ≤ 1
  noise_expand : 15 * U * ε ≤ β * ρ * φ ^ 2
  noise_contract : 12 * ε ≤ ρ ^ 2 * φ

def Balanced (c : Control) (x : State F E) : Prop :=
  (1 - 3 * c.β) * |x.a - x.q| ≤ |x.a + x.q| ∧ (1 - 3 * c.β) * |x.a + x.q| ≤ |x.a - x.q|

namespace Control

variable (c : Control)

lemma beta_pos : 0 < c.β := lt_of_lt_of_le c.rho_pos c.rho_le

lemma one_sub_ge : 5 / 8 ≤ 1 - 3 * c.β := by linarith [c.beta_le]

lemma rho_le_one : c.ρ ≤ 1 := c.rho_le.trans (by linarith [c.beta_le])

lemma rho_phi_le : c.ρ * c.φ ≤ 1 := by
  have h1 : c.ρ * c.φ ≤ 1 * c.φ := mul_le_mul_of_nonneg_right c.rho_le_one c.phi_pos.le
  linarith [c.phi_le]

lemma noise_swap : 2 * c.ε ≤ (5 / 16) * c.β * c.φ := by
  have h1 := c.noise_expand
  have hb := c.beta_pos
  have hφ := c.phi_pos
  have hbφ : 0 ≤ c.β * c.φ := by positivity
  have h2 : c.β * c.φ * (c.ρ * c.φ) ≤ c.β * c.φ * 1 := mul_le_mul_of_nonneg_left c.rho_phi_le hbφ
  have h3 : c.ε * 1 ≤ c.ε * c.U := mul_le_mul_of_nonneg_left c.U_ge c.eps_nonneg
  nlinarith

lemma noise_grow : c.ε ≤ c.ρ * (25 / 64) * c.φ := by
  have h := c.noise_contract
  have hρφ : 0 ≤ c.ρ * c.φ := by have := c.rho_pos; have := c.phi_pos; positivity
  have h1 : c.ρ * (c.ρ * c.φ) ≤ 1 * (c.ρ * c.φ) := mul_le_mul_of_nonneg_right c.rho_le_one hρφ
  have h2 : c.ρ ^ 2 * c.φ = c.ρ * (c.ρ * c.φ) := by ring
  linarith

lemma noise_small : c.ε ≤ c.φ / 100 := by
  have h := c.noise_contract
  have hφ := c.phi_pos
  have hρ2 : c.ρ ^ 2 ≤ 1 / 64 := by
    have := c.rho_pos; have := c.rho_le; have := c.beta_le; nlinarith
  have h1 : c.ρ ^ 2 * c.φ ≤ (1 / 64) * c.φ := mul_le_mul_of_nonneg_right hρ2 hφ.le
  linarith

end Control

section Algebra

variable {β ρ ε U φ b s h s' h' e : ℝ}

lemma balance_contract
    (hβ : β ≤ 1 / 8) (hρ : 0 < ρ) (hρβ : ρ ≤ β) (hbl : ρ ≤ |b|) (hbu : |b| ≤ β)
    (hφ : 0 < φ) (hswap : 2 * ε ≤ (5 / 16) * β * φ) (hgrow : ε ≤ ρ * (25 / 64) * φ)
    (hs' : s' = (1 + b) * s + e) (hh' : h' = (1 - b) * h + e) (he : |e| ≤ ε)
    (hbal : (1 - 3 * β) * |h| ≤ |s| ∧ (1 - 3 * β) * |s| ≤ |h|)
    (hlarge : (5 / 8) * φ ≤ |s| ∧ (5 / 8) * φ ≤ |h|)
    (hC : b * (s ^ 2 - h ^ 2) ≤ 0) :
    (1 - 3 * β) * |h'| ≤ |s'| ∧ (1 - 3 * β) * |s'| ≤ |h'| := by
  have hbu' := abs_le.mp hbu
  have hb1 : 0 < 1 + b := by linarith
  have hb2 : 0 < 1 - b := by linarith
  have hsn : 0 ≤ |s| := abs_nonneg s
  have hhn : 0 ≤ |h| := abs_nonneg h
  have hen : 0 ≤ |e| := abs_nonneg e
  have hβpos : 0 < β := lt_of_lt_of_le hρ hρβ
  have hone : 0 ≤ 1 - 3 * β := by linarith
  obtain ⟨hbal1, hbal2⟩ := hbal
  obtain ⟨hls, hlh⟩ := hlarge
  have hb0 : b ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hbl; linarith
  have hs_lo : (1 + b) * |s| - |e| ≤ |s'| := by
    rw [hs']
    have h2 := abs_sub_abs_le_abs_sub ((1 + b) * s) (-e)
    rw [sub_neg_eq_add, abs_neg, abs_mul, abs_of_pos hb1] at h2
    exact h2
  have hs_hi : |s'| ≤ (1 + b) * |s| + |e| := by
    rw [hs']
    have := abs_add_le ((1 + b) * s) e
    rw [abs_mul, abs_of_pos hb1] at this
    exact this
  have hh_lo : (1 - b) * |h| - |e| ≤ |h'| := by
    rw [hh']
    have h2 := abs_sub_abs_le_abs_sub ((1 - b) * h) (-e)
    rw [sub_neg_eq_add, abs_neg, abs_mul, abs_of_pos hb2] at h2
    exact h2
  have hh_hi : |h'| ≤ (1 - b) * |h| + |e| := by
    rw [hh']
    have := abs_add_le ((1 - b) * h) e
    rw [abs_mul, abs_of_pos hb2] at this
    exact this
  have hβe : 0 ≤ β * |e| := mul_nonneg hβpos.le hen
  have hAh : β * ((5 / 8) * φ) ≤ β * |h| := mul_le_mul_of_nonneg_left hlh hβpos.le
  have hAs : β * ((5 / 8) * φ) ≤ β * |s| := mul_le_mul_of_nonneg_left hls hβpos.le
  have heh : 2 * |e| ≤ β * |h| := by linarith
  have hρ1 : 0 ≤ ρ * (1 - 3 * β) := mul_nonneg hρ.le hone
  have hGh : ρ * (1 - 3 * β) * ((5 / 8) * φ) ≤ ρ * (1 - 3 * β) * |h| :=
    mul_le_mul_of_nonneg_left hlh hρ1
  have hGs : ρ * (1 - 3 * β) * ((5 / 8) * φ) ≤ ρ * (1 - 3 * β) * |s| :=
    mul_le_mul_of_nonneg_left hls hρ1
  have hρφ0 : 0 ≤ ρ * ((5 / 8) * φ) := by positivity
  have hG0 : ρ * (5 / 8) * ((5 / 8) * φ) ≤ ρ * (1 - 3 * β) * ((5 / 8) * φ) := by
    have h58 : (5 / 8 : ℝ) ≤ 1 - 3 * β := by linarith
    have := mul_le_mul_of_nonneg_right h58 hρφ0
    linarith
  have hgh : |e| ≤ ρ * (1 - 3 * β) * |h| := by linarith
  have hgs : |e| ≤ ρ * (1 - 3 * β) * |s| := by linarith
  have hMh := mul_le_mul_of_nonneg_left hh_hi hone
  have hMs := mul_le_mul_of_nonneg_left hs_hi hone
  rcases lt_or_gt_of_ne hb0 with hbneg | hbpos
  · have hsq : 0 ≤ s ^ 2 - h ^ 2 := by
      by_contra hlt
      push Not at hlt
      have := mul_pos_of_neg_of_neg hbneg hlt
      linarith
    have hhs : |h| ≤ |s| := by
      have : |h| ^ 2 ≤ |s| ^ 2 := by rw [sq_abs, sq_abs]; linarith
      exact (abs_le_of_sq_le_sq' this hsn).2
    have hρb : ρ ≤ -b := by rw [abs_of_neg hbneg] at hbl; exact hbl
    have hbh : 0 ≤ (β + b) * |h| := mul_nonneg (by linarith) hhn
    have hP2 : 0 ≤ β * ((-b) * |h|) := mul_nonneg hβpos.le (mul_nonneg (by linarith) hhn)
    have hhs1 : (1 + b) * |h| ≤ (1 + b) * |s| := mul_le_mul_of_nonneg_left hhs hb1.le
    have hQ1 : ρ * (1 - 3 * β) * |s| ≤ (-b) * (1 - 3 * β) * |s| := by
      have := mul_le_mul_of_nonneg_right hρb (mul_nonneg hone hsn)
      linarith
    have hhb2 : (1 - b) * ((1 - 3 * β) * |s|) ≤ (1 - b) * |h| :=
      mul_le_mul_of_nonneg_left hbal2 hb2.le
    constructor
    · linarith [hMh, hs_lo, hhs1, hbh, hP2, hβe, heh]
    · linarith [hMs, hh_lo, hhb2, hgs, hQ1, hβe]
  · have hsq : 0 ≤ h ^ 2 - s ^ 2 := by
      by_contra hlt
      push Not at hlt
      have : b * (s ^ 2 - h ^ 2) > 0 := mul_pos hbpos (by linarith)
      linarith
    have hsh : |s| ≤ |h| := by
      have : |s| ^ 2 ≤ |h| ^ 2 := by rw [sq_abs, sq_abs]; linarith
      exact (abs_le_of_sq_le_sq' this hhn).2
    have hρb : ρ ≤ b := by rw [abs_of_pos hbpos] at hbl; exact hbl
    have hbh' : 0 ≤ (β - b) * |h| := mul_nonneg (by linarith) hhn
    have hP2 : 0 ≤ β * (b * |h|) := mul_nonneg hβpos.le (mul_nonneg hbpos.le hhn)
    have hsh2 : (1 - 3 * β) * ((1 + b) * |s|) ≤ (1 - 3 * β) * ((1 + b) * |h|) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsh hb1.le) hone
    have hQ1 : ρ * (1 - 3 * β) * |h| ≤ b * (1 - 3 * β) * |h| := by
      have := mul_le_mul_of_nonneg_right hρb (mul_nonneg hone hhn)
      linarith
    have hhb1 : (1 + b) * ((1 - 3 * β) * |h|) ≤ (1 + b) * |s| :=
      mul_le_mul_of_nonneg_left hbal1 hb1.le
    constructor
    · linarith [hMh, hs_lo, hhb1, hgh, hQ1, hβe]
    · linarith [hMs, hh_lo, hsh2, hbh', hP2, hβe, heh]

lemma balance_expand
    (hβ : β ≤ 1 / 8) (hρ : 0 < ρ) (hρβ : ρ ≤ β) (hbl : ρ ≤ |b|) (hbu : |b| ≤ β)
    (hU : 1 ≤ U) (hφ : 0 < φ) (hρφ : ρ * φ ≤ 1)
    (hεn : 0 ≤ ε) (hswap : 2 * ε ≤ (5 / 16) * β * φ)
    (hexp : 15 * U * ε ≤ β * ρ * φ ^ 2)
    (hs' : s' = (1 + b) * s + e) (hh' : h' = (1 - b) * h + e) (he : |e| ≤ ε)
    (hlarge : (5 / 8) * φ ≤ |s| ∧ (5 / 8) * φ ≤ |h|)
    (hE : |b| * |s ^ 2 - h ^ 2| ≤ 4 * ε * U) (hpos : 0 < b * (s ^ 2 - h ^ 2)) :
    (1 - 3 * β) * |h'| ≤ |s'| ∧ (1 - 3 * β) * |s'| ≤ |h'| := by
  have hbu' := abs_le.mp hbu
  have hb1 : 0 < 1 + b := by linarith
  have hb2 : 0 < 1 - b := by linarith
  have hsn : 0 ≤ |s| := abs_nonneg s
  have hhn : 0 ≤ |h| := abs_nonneg h
  have hen : 0 ≤ |e| := abs_nonneg e
  have hβpos : 0 < β := lt_of_lt_of_le hρ hρβ
  have hone : 0 ≤ 1 - 3 * β := by linarith
  obtain ⟨hls, hlh⟩ := hlarge
  have hb0 : b ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hbl; linarith
  have hs_lo : (1 + b) * |s| - |e| ≤ |s'| := by
    rw [hs']
    have h2 := abs_sub_abs_le_abs_sub ((1 + b) * s) (-e)
    rw [sub_neg_eq_add, abs_neg, abs_mul, abs_of_pos hb1] at h2
    exact h2
  have hs_hi : |s'| ≤ (1 + b) * |s| + |e| := by
    rw [hs']
    have := abs_add_le ((1 + b) * s) e
    rw [abs_mul, abs_of_pos hb1] at this
    exact this
  have hh_lo : (1 - b) * |h| - |e| ≤ |h'| := by
    rw [hh']
    have h2 := abs_sub_abs_le_abs_sub ((1 - b) * h) (-e)
    rw [sub_neg_eq_add, abs_neg, abs_mul, abs_of_pos hb2] at h2
    exact h2
  have hh_hi : |h'| ≤ (1 - b) * |h| + |e| := by
    rw [hh']
    have := abs_add_le ((1 - b) * h) e
    rw [abs_mul, abs_of_pos hb2] at this
    exact this
  have hβe : 0 ≤ β * |e| := mul_nonneg hβpos.le hen
  have hAh : β * ((5 / 8) * φ) ≤ β * |h| := mul_le_mul_of_nonneg_left hlh hβpos.le
  have hAs : β * ((5 / 8) * φ) ≤ β * |s| := mul_le_mul_of_nonneg_left hls hβpos.le
  have heh : 2 * |e| ≤ β * |h| := by linarith
  have hes : 2 * |e| ≤ β * |s| := by linarith
  have hMh := mul_le_mul_of_nonneg_left hh_hi hone
  have hMs := mul_le_mul_of_nonneg_left hs_hi hone
  set g := |(|s| - |h|)| with hg_def
  have hg0 : 0 ≤ g := abs_nonneg _
  have hfac : |s ^ 2 - h ^ 2| = g * (|s| + |h|) := by
    have h1 : s ^ 2 - h ^ 2 = (|s| - |h|) * (|s| + |h|) := by
      rw [← sq_abs s, ← sq_abs h]; ring
    rw [h1, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |s| + |h|)]
  rw [hfac] at hE
  have hgap : ρ * ((5 / 8) * φ) * g ≤ 4 * ε * U := by
    have ha : ρ * ((5 / 8) * φ) ≤ |b| * (|s| + |h|) := by
      calc ρ * ((5 / 8) * φ) ≤ ρ * (|s| + |h|) := by
            apply mul_le_mul_of_nonneg_left _ hρ.le; linarith
        _ ≤ |b| * (|s| + |h|) := mul_le_mul_of_nonneg_right hbl (by positivity)
    have h1 := mul_le_mul_of_nonneg_right ha hg0
    have h2 : |b| * (|s| + |h|) * g = |b| * (g * (|s| + |h|)) := by ring
    linarith
  have hexp' : 4 * ε * U ≤ (4 / 15) * (β * ρ * φ ^ 2) := by linarith
  have hgρφ : g * (ρ * φ) ≤ (32 / 75) * β * φ * (ρ * φ) := by linarith
  have hg_le : g ≤ (32 / 75) * β * φ := le_of_mul_le_mul_right hgρφ (by positivity)
  have hεU : ε * 1 ≤ ε * U := mul_le_mul_of_nonneg_left hU hεn
  have hβφ : 0 ≤ β * φ := by positivity
  have hβρφ : β * φ * (ρ * φ) ≤ β * φ * 1 := mul_le_mul_of_nonneg_left hρφ hβφ
  have hε15 : 15 * ε ≤ β * φ := by linarith
  have hgap2 : g + 2 * |e| ≤ (5 / 8) * β * φ := by linarith
  have hgap3 : |h| ≤ |s| + g := by
    have := neg_abs_le (|s| - |h|); rw [← hg_def] at this; linarith
  have hgap4 : |s| ≤ |h| + g := by
    have := le_abs_self (|s| - |h|); rw [← hg_def] at this; linarith
  rcases lt_or_gt_of_ne hb0 with hbneg | hbpos
  · have hsq : 0 ≤ h ^ 2 - s ^ 2 := by
      by_contra hlt
      push Not at hlt
      have := mul_nonneg (neg_nonneg.mpr hbneg.le) (by linarith : 0 ≤ s ^ 2 - h ^ 2)
      linarith
    have hsh : |s| ≤ |h| := by
      have : |s| ^ 2 ≤ |h| ^ 2 := by rw [sq_abs, sq_abs]; linarith
      exact (abs_le_of_sq_le_sq' this hhn).2
    have hbs : 0 ≤ (β + b) * |s| := mul_nonneg (by linarith) hsn
    have hP3 : 0 ≤ β * ((-b) * |s|) := mul_nonneg hβpos.le (mul_nonneg (by linarith) hsn)
    have hbh0 : 0 ≤ (-b) * |h| := mul_nonneg (by linarith) hhn
    have hββh : β * (β * |h|) ≤ (1 / 8) * (β * |h|) :=
      mul_le_mul_of_nonneg_right hβ (mul_nonneg hβpos.le hhn)
    have hQb : β * ((-b) * |h|) ≤ β * (β * |h|) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hhn) hβpos.le
    have hsh2 : (1 - 3 * β) * ((1 + b) * |s|) ≤ (1 - 3 * β) * ((1 + b) * |h|) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsh hb1.le) hone
    have hg1 : (1 - 3 * β) * ((1 - b) * |h|) ≤ (1 - 3 * β) * ((1 - b) * (|s| + g)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgap3 hb2.le) hone
    have hgb : 0 ≤ g * (3 * β + b) := mul_nonneg hg0 (by linarith)
    have hgb2 : 0 ≤ β * ((-b) * g) := mul_nonneg hβpos.le (mul_nonneg (by linarith) hg0)
    constructor
    · linarith [hMh, hs_lo, hg1, hbs, hP3, hβe, hgap2, hAs, hgb, hgb2]
    · linarith [hMs, hh_lo, hsh2, hbh0, hQb, hββh, hβe, heh]
  · have hsq : 0 ≤ s ^ 2 - h ^ 2 := by
      by_contra hlt
      push Not at hlt
      have := mul_nonneg hbpos.le (by linarith : 0 ≤ h ^ 2 - s ^ 2)
      linarith
    have hhs : |h| ≤ |s| := by
      have : |h| ^ 2 ≤ |s| ^ 2 := by rw [sq_abs, sq_abs]; linarith
      exact (abs_le_of_sq_le_sq' this hsn).2
    have hbh' : 0 ≤ (β - b) * |h| := mul_nonneg (by linarith) hhn
    have hP2 : 0 ≤ β * (b * |h|) := mul_nonneg hβpos.le (mul_nonneg hbpos.le hhn)
    have hbs0 : 0 ≤ b * |s| := mul_nonneg hbpos.le hsn
    have hββs : β * (β * |s|) ≤ (1 / 8) * (β * |s|) :=
      mul_le_mul_of_nonneg_right hβ (mul_nonneg hβpos.le hsn)
    have hQs : β * (b * |s|) ≤ β * (β * |s|) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbu'.2 hsn) hβpos.le
    have hhs1 : (1 - 3 * β) * ((1 - b) * |h|) ≤ (1 - 3 * β) * ((1 - b) * |s|) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhs hb2.le) hone
    have hg1 : (1 - 3 * β) * ((1 + b) * |s|) ≤ (1 - 3 * β) * ((1 + b) * (|h| + g)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgap4 hb1.le) hone
    have hgb : 0 ≤ g * (3 * β - b) := mul_nonneg hg0 (by linarith)
    have hgb2 : 0 ≤ β * (b * g) := mul_nonneg hβpos.le (mul_nonneg hbpos.le hg0)
    constructor
    · linarith [hMh, hs_lo, hhs1, hbs0, hQs, hββs, hβe, hes]
    · linarith [hMs, hh_lo, hg1, hbh', hP2, hβe, hgap2, hAh, hgb, hgb2]

lemma balance_step
    (hβ : β ≤ 1 / 8) (hρ : 0 < ρ) (hρβ : ρ ≤ β) (hbl : ρ ≤ |b|) (hbu : |b| ≤ β)
    (hU : 1 ≤ U) (hφ : 0 < φ) (hρφ : ρ * φ ≤ 1)
    (hεn : 0 ≤ ε) (hswap : 2 * ε ≤ (5 / 16) * β * φ) (hgrow : ε ≤ ρ * (25 / 64) * φ)
    (hexp : 15 * U * ε ≤ β * ρ * φ ^ 2)
    (hs' : s' = (1 + b) * s + e) (hh' : h' = (1 - b) * h + e) (he : |e| ≤ ε)
    (hbal : (1 - 3 * β) * |h| ≤ |s| ∧ (1 - 3 * β) * |s| ≤ |h|)
    (hlarge : (5 / 8) * φ ≤ |s| ∧ (5 / 8) * φ ≤ |h|)
    (htype : b * (s ^ 2 - h ^ 2) ≤ 0 ∨ |b| * |s ^ 2 - h ^ 2| ≤ 4 * ε * U) :
    (1 - 3 * β) * |h'| ≤ |s'| ∧ (1 - 3 * β) * |s'| ≤ |h'| := by
  rcases htype with hC | hE
  · exact balance_contract hβ hρ hρβ hbl hbu hφ hswap hgrow hs' hh' he hbal hlarge hC
  · rcases le_or_gt (b * (s ^ 2 - h ^ 2)) 0 with hC | hpos
    · exact balance_contract hβ hρ hρβ hbl hbu hφ hswap hgrow hs' hh' he hbal hlarge hC
    · exact balance_expand hβ hρ hρβ hbl hbu hU hφ hρφ hεn hswap hexp hs' hh' he hlarge hE hpos

end Algebra

section Step

variable (c : Control) {x : State F E}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma balanced_mass (hx : Balanced c x) : (1 - 3 * c.β) * mass x ≤ phi x := by
  have hs : 0 ≤ |x.a + x.q| := abs_nonneg _
  have hh : 0 ≤ |x.a - x.q| := abs_nonneg _
  have hm : mass x = ((x.a + x.q) ^ 2 + (x.a - x.q) ^ 2) / 2 := by unfold mass; ring
  have hp : phi x = |x.a + x.q| * |x.a - x.q| := by
    unfold phi
    rw [← abs_mul]
    congr 1; ring
  rw [hm, hp, ← sq_abs (x.a + x.q), ← sq_abs (x.a - x.q)]
  obtain ⟨hx1, hx2⟩ := hx
  have hc := c.one_sub_ge
  have hc1 : 1 - 3 * c.β ≤ 1 := by linarith [c.beta_pos]
  nlinarith [mul_le_mul_of_nonneg_left hx1 hs, mul_le_mul_of_nonneg_left hx2 hh]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma balanced_large (hx : Balanced c x) (hφ : c.φ ^ 2 ≤ phi x) :
    (5 / 8) * c.φ ≤ |x.a + x.q| ∧ (5 / 8) * c.φ ≤ |x.a - x.q| := by
  have hp : phi x = |x.a + x.q| * |x.a - x.q| := by
    unfold phi; rw [← abs_mul]; congr 1; ring
  rw [hp] at hφ
  obtain ⟨hx1, hx2⟩ := hx
  have hc := c.one_sub_ge
  have hs := abs_nonneg (x.a + x.q)
  have hh := abs_nonneg (x.a - x.q)
  have hφ0 := c.phi_pos
  have hc1 : 1 - 3 * c.β ≤ 1 := by linarith [c.beta_pos]
  have hpos : (0 : ℝ) ≤ (5 / 8) * c.φ := by positivity
  constructor
  · have h1 : (1 - 3 * c.β) * c.φ ^ 2 ≤ |x.a + x.q| ^ 2 := by
      have := mul_le_mul_of_nonneg_left hx1 hs
      nlinarith [mul_le_mul_of_nonneg_left hφ (by linarith : (0:ℝ) ≤ 1 - 3 * c.β)]
    have h2 : ((5 / 8) * c.φ) ^ 2 ≤ |x.a + x.q| ^ 2 := by nlinarith [sq_nonneg c.φ]
    exact (abs_le_of_sq_le_sq' h2 hs).2
  · have h1 : (1 - 3 * c.β) * c.φ ^ 2 ≤ |x.a - x.q| ^ 2 := by
      have := mul_le_mul_of_nonneg_left hx2 hh
      nlinarith [mul_le_mul_of_nonneg_left hφ (by linarith : (0:ℝ) ≤ 1 - 3 * c.β)]
    have h2 : ((5 / 8) * c.φ) ^ 2 ≤ |x.a - x.q| ^ 2 := by nlinarith [sq_nonneg c.φ]
    exact (abs_le_of_sq_le_sq' h2 hh).2

end Step

end LongTails.Proofs.KernelPerceptronPhaseOne


namespace LongTails.Proofs.KernelPerceptronPhaseTwo

open KernelPerceptronDynamics

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

section Algebra

variable {β δ b ν res S S' Φ Φ' Q Q' D nS nΦ : ℝ}

lemma potential_step (hβ : 0 < β) (hβ1 : β ≤ 1 / 8) (hb : |b| ≤ β) (hδ : 0 < δ)
    (hF : b * ν + δ * res ≤ 0)
    (hS' : S' = S + 4 * b * ν + b ^ 2 * S + nS)
    (hΦ' : Φ' ≤ (1 - b ^ 2) * Φ + nΦ) (_hΦ0 : 0 ≤ Φ) (_hnΦ : 0 ≤ nΦ)
    (hSΦ : S ≤ Φ + 2 * |ν|)
    (hQ' : Q' ≤ Q + 2 * res - D) :
    Q' + (1 + β / (2 - β)) * (S' + Φ') / (2 * δ) ≤
      Q + (1 + β / (2 - β)) * (S + Φ) / (2 * δ) - D +
        (4 * β / (2 - β)) * (if 0 < b * ν then -res else 0) +
        (1 + β / (2 - β)) * (|nS| + nΦ) / (2 * δ) := by
  have h2β : 0 < 2 - β := by linarith
  have hγ : 1 + β / (2 - β) = 2 / (2 - β) := by field_simp; ring
  have hc : 4 * β / (2 - β) = 4 * β / (2 - β) := rfl
  have hbb : b ^ 2 ≤ β * |b| := by
    have : b ^ 2 = |b| * |b| := by rw [← sq_abs]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg b)
  have hleak : b ^ 2 * S ≤ b ^ 2 * Φ + 2 * β * |b * ν| := by
    have h1 : b ^ 2 * S ≤ b ^ 2 * (Φ + 2 * |ν|) := mul_le_mul_of_nonneg_left hSΦ (sq_nonneg b)
    have h2 : b ^ 2 * (2 * |ν|) ≤ β * |b| * (2 * |ν|) :=
      mul_le_mul_of_nonneg_right hbb (by positivity)
    rw [abs_mul]
    nlinarith
  have hnS : nS ≤ |nS| := le_abs_self nS
  suffices h : 2 * δ * (Q' + (1 + β / (2 - β)) * (S' + Φ') / (2 * δ)) ≤
      2 * δ * (Q + (1 + β / (2 - β)) * (S + Φ) / (2 * δ) - D +
        (4 * β / (2 - β)) * (if 0 < b * ν then -res else 0) +
        (1 + β / (2 - β)) * (|nS| + nΦ) / (2 * δ)) by
    exact le_of_mul_le_mul_left h (by positivity)
  have hδ2 : (2 * δ) ≠ 0 := by positivity
  have e1 : 2 * δ * (Q' + (1 + β / (2 - β)) * (S' + Φ') / (2 * δ)) =
      2 * δ * Q' + (1 + β / (2 - β)) * (S' + Φ') := by field_simp
  have e2 : 2 * δ * (Q + (1 + β / (2 - β)) * (S + Φ) / (2 * δ) - D +
        (4 * β / (2 - β)) * (if 0 < b * ν then -res else 0) +
        (1 + β / (2 - β)) * (|nS| + nΦ) / (2 * δ)) =
      2 * δ * Q - 2 * δ * D + 2 * δ * (4 * β / (2 - β)) * (if 0 < b * ν then -res else 0) +
        (1 + β / (2 - β)) * (S + Φ) + (1 + β / (2 - β)) * (|nS| + nΦ) := by
    field_simp; ring
  rw [e1, e2, hγ]
  have hQ : 2 * δ * Q' ≤ 2 * δ * Q + 4 * δ * res - 2 * δ * D := by nlinarith
  have hSΦ' : (2 / (2 - β)) * (S' + Φ') ≤
      (2 / (2 - β)) * (S + Φ) + (2 / (2 - β)) * (4 * b * ν + 2 * β * |b * ν| + |nS| + nΦ) := by
    have hpos : 0 ≤ 2 / (2 - β) := by positivity
    have : S' + Φ' ≤ S + Φ + 4 * b * ν + 2 * β * |b * ν| + |nS| + nΦ := by
      nlinarith
    nlinarith
  have hγpos : 0 < 2 / (2 - β) := by positivity
  split_ifs with hpos
  · -- expanding step: bν > 0, so |bν| = bν ≤ δ(-res)
    have habs : |b * ν| = b * ν := abs_of_pos hpos
    have hviol : b * ν ≤ δ * (-res) := by linarith
    rw [habs] at hSΦ'
    have key : (2 / (2 - β)) * (4 * b * ν + 2 * β * (b * ν)) - 4 * (b * ν) =
        2 * (4 * β / (2 - β)) * (b * ν) := by field_simp; ring
    have hres : 4 * δ * res = -4 * (δ * (-res)) := by ring
    have hmono : 2 * (4 * β / (2 - β)) * (b * ν) ≤ 2 * (4 * β / (2 - β)) * (δ * (-res)) := by
      apply mul_le_mul_of_nonneg_left hviol; positivity
    have hF4 : 4 * δ * res + 4 * (b * ν) ≤ 0 := by linarith
    linarith [key, hmono, hF4, hQ, hSΦ']
  · -- contracting or tie step: bν ≤ 0, so |bν| = -bν and the first-order terms cancel
    have hle : b * ν ≤ 0 := le_of_not_gt hpos
    have habs : |b * ν| = -(b * ν) := abs_of_nonpos hle
    rw [habs] at hSΦ'
    have key : (2 / (2 - β)) * (4 * b * ν + 2 * β * (-(b * ν))) = 4 * (b * ν) := by
      field_simp; ring
    have hres : 4 * δ * res ≤ -4 * (b * ν) := by linarith
    linarith [key, hres, hQ, hSΦ']

end Algebra

section Violation

variable {Λ κstar U : ℝ} {w : E} {p : E} {R : F →L[ℝ] E} {x : State F E}

omit [CompleteSpace E] [CompleteSpace F] in
lemma violation_bound (hΔ : κstar ≤ ⟪w, move p R x⟫) (hU : ‖move p R x‖ ≤ U)
    (hΛ : 0 ≤ Λ) :
    -res p R x ≤ U * ‖x.z - Λ • w‖ - Λ * κstar := by
  rw [res_eq_inner]
  have h1 : ⟪x.z, move p R x⟫ = ⟪x.z - Λ • w, move p R x⟫ + Λ * ⟪w, move p R x⟫ := by
    rw [inner_sub_left, real_inner_smul_left]; ring
  have h2 : -⟪x.z - Λ • w, move p R x⟫ ≤ ‖x.z - Λ • w‖ * ‖move p R x‖ := by
    have := abs_real_inner_le_norm (x.z - Λ • w) (move p R x)
    linarith [neg_abs_le ⟪x.z - Λ • w, move p R x⟫]
  have h3 : ‖x.z - Λ • w‖ * ‖move p R x‖ ≤ ‖x.z - Λ • w‖ * U :=
    mul_le_mul_of_nonneg_left hU (norm_nonneg _)
  have h4 : Λ * κstar ≤ Λ * ⟪w, move p R x⟫ := mul_le_mul_of_nonneg_left hΔ hΛ
  nlinarith

omit [CompleteSpace E] [CompleteSpace F] in
lemma move_inner_margin {κ : ℝ} (hw : ‖w‖ = 1) (hp : ‖p‖ ≤ 1) (hr : κ ≤ ⟪w, R x.t⟫) :
    κ - |x.a| ≤ ⟪w, move p R x⟫ := by
  simp only [move, inner_add_right, real_inner_smul_right]
  have h1 : |⟪w, p⟫| ≤ 1 := by
    have := abs_real_inner_le_norm w p
    rw [hw, one_mul] at this
    exact this.trans hp
  have h2 : -|x.a| ≤ x.a * ⟪w, p⟫ := by
    have h3 : |x.a * ⟪w, p⟫| ≤ |x.a| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) h1
    linarith [neg_abs_le (x.a * ⟪w, p⟫)]
  linarith

lemma Q_step {Λ : ℝ} (w : E) (b δ : ℝ) (p : E) (R : F →L[ℝ] E) (x : State F E) :
    ‖(step b δ p R x).z - Λ • w‖ ^ 2 =
      ‖x.z - Λ • w‖ ^ 2 + 2 * res p R x - 2 * Λ * ⟪w, move p R x⟫ + ‖move p R x‖ ^ 2 := by
  rw [step_z, show x.z + move p R x - Λ • w = (x.z - Λ • w) + move p R x by abel,
    norm_add_sq_real, res_eq_inner, inner_sub_left, real_inner_smul_left]
  ring

end Violation

noncomputable def potential (Λ β δ : ℝ) (w : E) (x : State F E) : ℝ :=
  ‖x.z - Λ • w‖ ^ 2 + (1 + β / (2 - β)) * (mass x + phi x) / (2 * δ)

noncomputable def violation (b : ℝ) (p : E) (R : F →L[ℝ] E) (x : State F E) : ℝ :=
  if 0 < b * bias x then -res p R x else 0

noncomputable def noiseMass (b δ : ℝ) (p : E) (x : State F E) : ℝ :=
  |2 * noise δ p x * (x.a + b * x.q) + noise δ p x ^ 2|

noncomputable def noisePhi (b δ : ℝ) (p : E) (x : State F E) : ℝ :=
  |noise δ p x| * (|(1 + b) * (x.a + x.q)| + |(1 - b) * (x.a - x.q)|) + noise δ p x ^ 2

omit [CompleteSpace E] [CompleteSpace F] in
lemma violation_nonneg {b δ : ℝ} {p : E} {R : F →L[ℝ] E} {x : State F E} (hδ : 0 < δ)
    (hF : misclassified b δ p R x) : 0 ≤ violation b p R x := by
  unfold violation
  split_ifs with h
  · have := delta_res_le b δ p R x hF
    unfold bias at h
    have : δ * res p R x < 0 := by unfold bias at this; linarith
    have := (mul_neg_iff.mp this)
    rcases this with ⟨_, hr⟩ | ⟨hδ', _⟩
    · linarith
    · linarith
  · exact le_refl 0

section StatePotential

variable {Λ β δ b κstar U : ℝ} {w p : E} {R : F →L[ℝ] E} {x : State F E}

lemma potential_step_state (hβ : 0 < β) (hβ1 : β ≤ 1 / 8) (hb : |b| ≤ β) (hδ : 0 < δ)
    (hF : misclassified b δ p R x) (hw : ‖w‖ = 1) (hp : ‖p‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hκ : κstar ≤ ⟪w, R x.t⟫ - |x.a|) (hΛ : 0 ≤ Λ)
    (hU : |x.a| + ‖x.t‖ ≤ U) :
    potential Λ β δ w (step b δ p R x) ≤ potential Λ β δ w x - (2 * Λ * κstar - U ^ 2) +
      (4 * β / (2 - β)) * violation b p R x +
      (1 + β / (2 - β)) * (noiseMass b δ p x + noisePhi b δ p x) / (2 * δ) := by
  unfold potential violation
  have hmove := move_norm_le p R x hp hR
  have hmoveU : ‖move p R x‖ ≤ U := hmove.trans hU
  have hmargin := move_inner_margin (κ := ⟪w, R x.t⟫) hw hp (le_refl _)
  have hQ' : ‖(step b δ p R x).z - Λ • w‖ ^ 2 ≤
      ‖x.z - Λ • w‖ ^ 2 + 2 * res p R x - (2 * Λ * κstar - U ^ 2) := by
    rw [Q_step]
    have h1 : Λ * κstar ≤ Λ * ⟪w, move p R x⟫ := mul_le_mul_of_nonneg_left (hκ.trans hmargin) hΛ
    have h2 : ‖move p R x‖ ^ 2 ≤ U ^ 2 := by
      have := norm_nonneg (move p R x)
      nlinarith
    nlinarith
  have hS' := step_mass b δ p R x
  have hb2 : b ^ 2 ≤ 1 := by
    have := abs_le.mp hb
    nlinarith [abs_nonneg b, sq_abs b]
  have hΦ' : phi (step b δ p R x) ≤ (1 - b ^ 2) * phi x +
      (|noise δ p x| * (|(1 + b) * (x.a + x.q)| + |(1 - b) * (x.a - x.q)|) + noise δ p x ^ 2) := by
    have := step_phi_le b δ p R x hb2
    linarith
  have hSΦ := mass_le_phi_add x
  have hmis : b * bias x + δ * res p R x ≤ 0 := by
    unfold misclassified at hF; unfold bias; linarith
  have := potential_step (ν := bias x) (res := res p R x) (S := mass x)
    (S' := mass (step b δ p R x)) (Φ := phi x) (Φ' := phi (step b δ p R x))
    (Q := ‖x.z - Λ • w‖ ^ 2) (Q' := ‖(step b δ p R x).z - Λ • w‖ ^ 2)
    (D := 2 * Λ * κstar - U ^ 2)
    (nS := 2 * noise δ p x * (x.a + b * x.q) + noise δ p x ^ 2)
    (nΦ := |noise δ p x| * (|(1 + b) * (x.a + x.q)| + |(1 - b) * (x.a - x.q)|) + noise δ p x ^ 2)
    hβ hβ1 hb hδ hmis hS' hΦ' (abs_nonneg _) (by positivity) hSΦ hQ'
  unfold noiseMass noisePhi
  exact this

end StatePotential

end LongTails.Proofs.KernelPerceptronPhaseTwo


namespace LongTails.Proofs.KernelPerceptronTrajectory

open KernelPerceptronDynamics
open KernelPerceptronPhaseOne (balanced_mass balanced_large balance_step)
open KernelPerceptronPhaseTwo

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

structure Geometry (ρ β κ₀ : ℝ) (b : ι → ℝ) (p : ι → E) (R : ι → F →L[ℝ] E) (w : E) (t₀ : F) :
    Prop where
  bl : ∀ i, ρ ≤ |b i|
  bu : ∀ i, |b i| ≤ β
  pn : ∀ i, ‖p i‖ ≤ 1
  Rn : ∀ i, ‖R i‖ ≤ 1
  wn : ‖w‖ = 1
  margin : ∀ i, κ₀ ≤ ⟪w, R i t₀⟫

section Generic

variable {b : ι → ℝ} {δ a₀ : ℝ} {p : ι → E} {R : ι → F →L[ℝ] E} {t₀ : F}
  {x : ℕ → State F E} {i : ℕ → ι} {K : ℕ}

lemma z_step_norm (tr : Trajectory b δ p R a₀ t₀ x i K) (G : ∀ j, ‖p j‖ ≤ 1 ∧ ‖R j‖ ≤ 1)
    {k : ℕ} (hk : k < K) :
    ‖(x (k + 1)).z‖ ≤ ‖(x k).z‖ + (|(x k).a| + ‖(x k).t‖) := by
  rw [tr.update k hk, step_z]
  exact (norm_add_le _ _).trans
    (by linarith [move_norm_le (p (i k)) (R (i k)) (x k) (G (i k)).1 (G (i k)).2])

lemma t_step (tr : Trajectory b δ p R a₀ t₀ x i K) (G : ∀ j, ‖p j‖ ≤ 1 ∧ ‖R j‖ ≤ 1) (hδ : 0 ≤ δ)
    {k : ℕ} (hk : k < K) :
    ‖(x (k + 1)).t - (x k).t‖ ≤ δ * ‖(x k).z‖ := by
  rw [tr.update k hk]
  exact t_step_norm (b (i k)) δ (p (i k)) (R (i k)) (x k) (G (i k)).2 hδ

omit [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma start_phi (a₀ : ℝ) (t₀ : F) : phi (start a₀ t₀ : State F E) = a₀ ^ 2 := by
  unfold phi start
  simp only [sq, mul_zero, sub_zero]
  rw [abs_of_nonneg (mul_self_nonneg a₀)]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma start_mass (a₀ : ℝ) (t₀ : F) : mass (start a₀ t₀ : State F E) = a₀ ^ 2 := by
  unfold mass start
  simp

omit [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma start_balanced (c : KernelPerceptronPhaseOne.Control) (a₀ : ℝ) (t₀ : F) :
    KernelPerceptronPhaseOne.Balanced c (start a₀ t₀ : State F E) := by
  unfold KernelPerceptronPhaseOne.Balanced start
  simp only [add_zero, sub_zero]
  have := c.beta_pos
  have := abs_nonneg a₀
  constructor <;> nlinarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma start_z (a₀ : ℝ) (t₀ : F) : ‖(start a₀ t₀ : State F E).z‖ = 0 := by simp [start]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma start_t (a₀ : ℝ) (t₀ : F) : (start a₀ t₀ : State F E).t = t₀ := rfl

end Generic

section OneStepPhaseOne

variable (c : KernelPerceptronPhaseOne.Control) {b δ : ℝ} {p : E} {R : F →L[ℝ] E}
  {y : State F E}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma balanced_sum_bound (hy : KernelPerceptronPhaseOne.Balanced c y) :
    |y.a + y.q| + |y.a - y.q| ≤ 2 * Real.sqrt (phi y / (1 - 3 * c.β)) := by
  have hc := c.one_sub_ge
  have hs := abs_nonneg (y.a + y.q)
  have hh := abs_nonneg (y.a - y.q)
  have hp : phi y = |y.a + y.q| * |y.a - y.q| := by
    unfold phi; rw [← abs_mul]; congr 1; ring
  obtain ⟨h1, h2⟩ := hy
  have key : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → (1 - 3 * c.β) * u ≤ v →
      u ≤ Real.sqrt (u * v / (1 - 3 * c.β)) := by
    intro u v hu hv huv
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left huv hu
    nlinarith
  have hA := key _ _ hs hh h2
  have hB := key _ _ hh hs h1
  rw [mul_comm |y.a - y.q| |y.a + y.q|] at hB
  rw [hp]
  linarith

omit [CompleteSpace E] [CompleteSpace F] in
lemma step_type (hδ : 0 < δ) (hp : ‖p‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hmis : misclassified b δ p R y) (hU : |y.a| + ‖y.t‖ ≤ c.U) (hz : δ * ‖y.z‖ ≤ c.ε) :
    b * ((y.a + y.q) ^ 2 - (y.a - y.q) ^ 2) ≤ 0 ∨
      |b| * |(y.a + y.q) ^ 2 - (y.a - y.q) ^ 2| ≤ 4 * c.ε * c.U := by
  have hU0 : 0 ≤ c.U := by linarith [c.U_ge]
  have hid : (y.a + y.q) ^ 2 - (y.a - y.q) ^ 2 = 4 * (y.a * y.q) := by ring
  rw [hid]
  rcases le_or_gt (b * (4 * (y.a * y.q))) 0 with h | h
  · exact Or.inl h
  · right
    have hres := delta_res_le b δ p R y hmis
    unfold bias at hres
    have hres_abs := res_abs_le p R y hp hR
    have h1 : b * (y.a * y.q) ≤ δ * |res p R y| := by
      have := neg_abs_le (res p R y)
      have h5 : δ * (-|res p R y|) ≤ δ * res p R y := mul_le_mul_of_nonneg_left this hδ.le
      linarith
    have h2 : δ * |res p R y| ≤ δ * ((|y.a| + ‖y.t‖) * ‖y.z‖) :=
      mul_le_mul_of_nonneg_left hres_abs hδ.le
    have h3 : δ * ((|y.a| + ‖y.t‖) * ‖y.z‖) ≤ c.U * c.ε := by
      have : δ * ((|y.a| + ‖y.t‖) * ‖y.z‖) = (|y.a| + ‖y.t‖) * (δ * ‖y.z‖) := by ring
      rw [this]
      exact mul_le_mul hU hz (by positivity) hU0
    have habs : |b| * |4 * (y.a * y.q)| = 4 * (b * (y.a * y.q)) := by
      rw [← abs_mul, abs_of_pos (by linarith)]
      ring
    rw [habs]
    linarith

lemma balance_preserved (hδ : 0 < δ) (hp : ‖p‖ ≤ 1) (hR : ‖R‖ ≤ 1) (hbl : c.ρ ≤ |b|)
    (hbu : |b| ≤ c.β) (hbal : KernelPerceptronPhaseOne.Balanced c y) (hφ : c.φ ^ 2 ≤ phi y)
    (hmis : misclassified b δ p R y) (hU : |y.a| + ‖y.t‖ ≤ c.U) (hz : δ * ‖y.z‖ ≤ c.ε) :
    KernelPerceptronPhaseOne.Balanced c (step b δ p R y) := by
  have hnoise : |noise δ p y| ≤ c.ε := (noise_abs_le δ p y hp hδ.le).trans hz
  have hl := balanced_large c hbal hφ
  have htype := step_type c hδ hp hR hmis hU hz
  exact balance_step c.beta_le c.rho_pos c.rho_le hbl hbu c.U_ge c.phi_pos c.rho_phi_le
    c.eps_nonneg c.noise_swap c.noise_grow c.noise_expand
    (step_sum b δ p R y) (step_diff b δ p R y) hnoise hbal hl htype

lemma contraction (hδ : 0 < δ) (hp : ‖p‖ ≤ 1) (hbl : c.ρ ≤ |b|) (hbu : |b| ≤ c.β)
    (hbal : KernelPerceptronPhaseOne.Balanced c y) (hφ : c.φ ^ 2 ≤ phi y)
    (hz : δ * ‖y.z‖ ≤ c.ε) :
    phi (step b δ p R y) ≤ (1 - c.ρ ^ 2 / 2) * phi y := by
  have hnoise : |noise δ p y| ≤ c.ε := (noise_abs_le δ p y hp hδ.le).trans hz
  have hone := c.one_sub_ge
  have hbu' := abs_le.mp hbu
  have hb2 : b ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) (by linarith [c.beta_le])
  have hstep := step_phi_le b δ p R y hb2
  have hρb : c.ρ ^ 2 ≤ b ^ 2 := by
    rw [← sq_abs b]
    exact pow_le_pow_left₀ c.rho_pos.le hbl 2
  have hphi0 : 0 ≤ phi y := abs_nonneg _
  have hcontr : (1 - b ^ 2) * phi y ≤ (1 - c.ρ ^ 2) * phi y := by
    apply mul_le_mul_of_nonneg_right _ hphi0
    linarith
  have hsum := balanced_sum_bound c hbal
  set L := Real.sqrt (phi y / (1 - 3 * c.β)) with hL
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hL2 : L ^ 2 = phi y / (1 - 3 * c.β) := Real.sq_sqrt (div_nonneg hphi0 (by linarith))
  have hφL : c.φ ≤ L := by
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ (by linarith)]
    have : c.φ ^ 2 * (1 - 3 * c.β) ≤ c.φ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left (by linarith [c.beta_pos]) (sq_nonneg _)
    linarith
  have hεL : c.ε ≤ c.ρ ^ 2 * L / 12 := by
    have h1 := c.noise_contract
    have h2 : c.ρ ^ 2 * c.φ ≤ c.ρ ^ 2 * L := mul_le_mul_of_nonneg_left hφL (sq_nonneg _)
    linarith
  have habs1 : |(1 + b) * (y.a + y.q)| ≤ (1 + c.β) * |y.a + y.q| := by
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    rw [abs_le]; constructor <;> linarith
  have habs2 : |(1 - b) * (y.a - y.q)| ≤ (1 + c.β) * |y.a - y.q| := by
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    rw [abs_le]; constructor <;> linarith
  have hβ1 : 0 ≤ 1 + c.β := by linarith [c.beta_pos]
  have hsum2 : |(1 + b) * (y.a + y.q)| + |(1 - b) * (y.a - y.q)| ≤ (1 + c.β) * (2 * L) := by
    have := mul_le_mul_of_nonneg_left hsum hβ1
    linarith
  have hA : |noise δ p y| * (|(1 + b) * (y.a + y.q)| + |(1 - b) * (y.a - y.q)|) ≤
      c.ε * ((1 + c.β) * (2 * L)) :=
    mul_le_mul hnoise hsum2 (by positivity) c.eps_nonneg
  have hB : noise δ p y ^ 2 ≤ c.ε ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hnoise 2
  have hC : c.ε * ((1 + c.β) * (2 * L)) ≤ (c.ρ ^ 2 * L / 12) * ((1 + c.β) * (2 * L)) :=
    mul_le_mul_of_nonneg_right hεL (by positivity)
  have hD : c.ε ^ 2 ≤ (c.ρ ^ 2 * L / 12) ^ 2 := pow_le_pow_left₀ c.eps_nonneg hεL 2
  have hρ1 : c.ρ ^ 2 ≤ 1 / 64 := by
    have h1 := c.rho_pos
    have h4 : c.ρ ≤ 1 / 8 := c.rho_le.trans c.beta_le
    nlinarith [h1, h4]
  have hLphi : L ^ 2 ≤ (8 / 5) * phi y := by
    rw [hL2, div_le_iff₀ (by linarith)]
    have : (5 / 8 : ℝ) * phi y ≤ (1 - 3 * c.β) * phi y := mul_le_mul_of_nonneg_right hone hphi0
    linarith
  have hβ8 : (1 + c.β) * (2 * L) ≤ (9 / 8) * (2 * L) :=
    mul_le_mul_of_nonneg_right (by linarith [c.beta_le]) (by positivity)
  have hE : (c.ρ ^ 2 * L / 12) * ((1 + c.β) * (2 * L)) ≤
      (c.ρ ^ 2 * L / 12) * ((9 / 8) * (2 * L)) :=
    mul_le_mul_of_nonneg_left hβ8 (by positivity)
  have hLL : 0 ≤ c.ρ ^ 2 * L ^ 2 := by positivity
  have hF : (c.ρ ^ 2 * L / 12) ^ 2 ≤ c.ρ ^ 2 * L ^ 2 / 144 := by
    have : (c.ρ ^ 2 * L / 12) ^ 2 = c.ρ ^ 2 * (c.ρ ^ 2 * L ^ 2) / 144 := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right hρ1 hLL
    linarith
  have hG : c.ρ ^ 2 * L ^ 2 ≤ c.ρ ^ 2 * ((8 / 5) * phi y) :=
    mul_le_mul_of_nonneg_left hLphi (sq_nonneg _)
  have hρφ0 : 0 ≤ c.ρ ^ 2 * phi y := by positivity
  have hnoise_tot : |noise δ p y| * (|(1 + b) * (y.a + y.q)| + |(1 - b) * (y.a - y.q)|) +
      noise δ p y ^ 2 ≤ c.ρ ^ 2 / 2 * phi y := by
    linarith [hA, hB, hC, hD, hE, hF, hG, hρφ0]
  calc phi (step b δ p R y) ≤ (1 - c.ρ ^ 2) * phi y + c.ρ ^ 2 / 2 * phi y := by linarith
    _ = (1 - c.ρ ^ 2 / 2) * phi y := by ring

end OneStepPhaseOne

section PhaseOne

variable (c : KernelPerceptronPhaseOne.Control)
variable {b : ι → ℝ} {δ a₀ κ₀ : ℝ} {p : ι → E} {R : ι → F →L[ℝ] E} {w : E} {t₀ : F}
  {x : ℕ → State F E} {i : ℕ → ι} {K : ℕ}

structure PhaseOneState (δ a₀ : ℝ) (t₀ : F) (M : ℕ) (x : State F E) (k : ℕ) : Prop where
  balanced : KernelPerceptronPhaseOne.Balanced c x
  phi_le : phi x ≤ (1 - c.ρ ^ 2 / 2) ^ k * a₀ ^ 2
  z_le : ‖x.z‖ ≤ c.U * k
  drift : ‖x.t - t₀‖ ≤ δ * c.U * M * k

omit [InnerProductSpace ℝ E] [CompleteSpace E] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma phaseOne_initial (δ a₀ : ℝ) (t₀ : F) (M : ℕ) :
    PhaseOneState c δ a₀ t₀ M (start a₀ t₀ : State F E) 0 where
  balanced := start_balanced c a₀ t₀
  phi_le := by rw [start_phi]; simp
  z_le := by rw [start_z]; simp
  drift := by rw [start_t]; simp

lemma phaseOne_step (hδ : 0 < δ) (G : Geometry c.ρ c.β κ₀ b p R w t₀) {M : ℕ} {τ : ℝ}
    (hε : δ * c.U * M ≤ c.ε)
    (hUa : Real.sqrt (a₀ ^ 2 / (1 - 3 * c.β)) + ‖t₀‖ + τ ≤ c.U)
    (hτ : δ * c.U * M * M ≤ τ)
    (tr : Trajectory b δ p R a₀ t₀ x i K) {k : ℕ} (hk : k < K) (hkM : k < M)
    (hs : PhaseOneState c δ a₀ t₀ M (x k) k) (hφ : c.φ ^ 2 ≤ phi (x k)) :
    PhaseOneState c δ a₀ t₀ M (x (k + 1)) (k + 1) := by
  have hone := c.one_sub_ge
  have hU1 := c.U_ge
  have hU0 : 0 ≤ c.U := by linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hδU : 0 ≤ δ * c.U := mul_nonneg hδ.le hU0
  have hδUM : 0 ≤ δ * c.U * M := mul_nonneg hδU hM0
  have hkM' : (k : ℝ) ≤ M := by exact_mod_cast hkM.le
  set y := x k with hy
  have hmass : (1 - 3 * c.β) * mass y ≤ phi y := balanced_mass c hs.balanced
  have hpow : (1 - c.ρ ^ 2 / 2) ^ k ≤ 1 := by
    apply pow_le_one₀ <;> nlinarith [c.rho_pos, c.rho_le_one]
  have hphi_le : phi y ≤ a₀ ^ 2 := by
    have h1 := hs.phi_le
    have h2 := mul_le_mul_of_nonneg_right hpow (sq_nonneg a₀)
    linarith
  have hmass_le : mass y ≤ a₀ ^ 2 / (1 - 3 * c.β) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have ha : |y.a| ≤ Real.sqrt (a₀ ^ 2 / (1 - 3 * c.β)) :=
    (abs_a_le_sqrt_mass y).trans (Real.sqrt_le_sqrt hmass_le)
  have hdrift : ‖y.t - t₀‖ ≤ τ := by
    have h1 := hs.drift
    have h2 : δ * c.U * M * k ≤ δ * c.U * M * M := mul_le_mul_of_nonneg_left hkM' hδUM
    linarith
  have htn : ‖y.t‖ ≤ ‖t₀‖ + τ := by
    have := norm_sub_norm_le y.t t₀
    linarith
  have hU : |y.a| + ‖y.t‖ ≤ c.U := by linarith
  have hz : δ * ‖y.z‖ ≤ c.ε := by
    have h1 : ‖y.z‖ ≤ c.U * k := hs.z_le
    have h2 : δ * ‖y.z‖ ≤ δ * (c.U * k) := mul_le_mul_of_nonneg_left h1 hδ.le
    have h3 : (δ * c.U) * k ≤ (δ * c.U) * M := mul_le_mul_of_nonneg_left hkM' hδU
    have h4 : δ * (c.U * k) = (δ * c.U) * k := by ring
    linarith
  have hmis := tr.mistake k hk
  have hup := tr.update k hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hup]
    exact balance_preserved c hδ (G.pn _) (G.Rn _) (G.bl _) (G.bu _) hs.balanced hφ hmis hU hz
  · rw [hup]
    have h1 := contraction c (R := R (i k)) hδ (G.pn (i k)) (G.bl (i k)) (G.bu (i k))
      hs.balanced hφ hz
    have h2 : (1 - c.ρ ^ 2 / 2) * phi y ≤
        (1 - c.ρ ^ 2 / 2) * ((1 - c.ρ ^ 2 / 2) ^ k * a₀ ^ 2) := by
      apply mul_le_mul_of_nonneg_left hs.phi_le
      nlinarith [c.rho_pos, c.rho_le_one]
    calc phi (step (b (i k)) δ (p (i k)) (R (i k)) y) ≤ (1 - c.ρ ^ 2 / 2) * phi y := h1
      _ ≤ (1 - c.ρ ^ 2 / 2) * ((1 - c.ρ ^ 2 / 2) ^ k * a₀ ^ 2) := h2
      _ = (1 - c.ρ ^ 2 / 2) ^ (k + 1) * a₀ ^ 2 := by ring
  · have h1 := z_step_norm tr (fun j => ⟨G.pn j, G.Rn j⟩) hk
    have h2 := hs.z_le
    push_cast
    linarith
  · have h1 := hs.drift
    have h2 := t_step tr (fun j => ⟨G.pn j, G.Rn j⟩) hδ.le hk
    have h3 : ‖(x (k + 1)).t - t₀‖ ≤ ‖(x (k + 1)).t - y.t‖ + ‖y.t - t₀‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h4 : δ * ‖y.z‖ ≤ δ * c.U * M := by
      have h5 : ‖y.z‖ ≤ c.U * k := hs.z_le
      have h6 : δ * ‖y.z‖ ≤ δ * (c.U * k) := mul_le_mul_of_nonneg_left h5 hδ.le
      have h7 : (δ * c.U) * k ≤ (δ * c.U) * M := mul_le_mul_of_nonneg_left hkM' hδU
      have h8 : δ * (c.U * k) = (δ * c.U) * k := by ring
      linarith
    push_cast
    linarith

lemma phaseOne_invariant (hδ : 0 < δ) (G : Geometry c.ρ c.β κ₀ b p R w t₀) {M : ℕ} {τ : ℝ}
    (hε : δ * c.U * M ≤ c.ε)
    (hUa : Real.sqrt (a₀ ^ 2 / (1 - 3 * c.β)) + ‖t₀‖ + τ ≤ c.U)
    (hτ : δ * c.U * M * M ≤ τ)
    (tr : Trajectory b δ p R a₀ t₀ x i K) :
    ∀ k, k ≤ K → k ≤ M → (∀ j, j < k → c.φ ^ 2 ≤ phi (x j)) →
      PhaseOneState c δ a₀ t₀ M (x k) k := by
  intro k
  induction k with
  | zero =>
    intro _ _ _
    rw [tr.initial]
    exact phaseOne_initial c δ a₀ t₀ M
  | succ n ih =>
    intro hK hM hφ
    have hn := ih (by omega) (by omega) (fun j hj => hφ j (by omega))
    exact phaseOne_step c hδ G hε hUa hτ tr (by omega) (by omega) hn (hφ n (by omega))

end PhaseOne

section PhaseTwo

structure Control where
  Λ : ℝ
  κstar : ℝ
  κ₀ : ℝ
  U : ℝ
  β : ℝ
  δ : ℝ
  Wbar : ℝ
  ω : ℝ
  σ : ℝ
  ζ : ℝ
  nbar : ℝ
  τ₁ : ℝ
  τ₂ : ℝ
  tnorm : ℝ
  beta_pos : 0 < β
  beta_le : β ≤ 1 / 8
  delta_pos : 0 < δ
  lambda_nonneg : 0 ≤ Λ
  kstar_pos : 0 < κstar
  U_pos : 0 < U
  omega_nonneg : 0 ≤ ω
  sigma_nonneg : 0 ≤ σ
  tau1_nonneg : 0 ≤ τ₁
  tau2_nonneg : 0 ≤ τ₂
  wbar_nonneg : 0 ≤ Wbar
  wbar_le : Wbar ≤ ω ^ 2
  mass_le : 2 * δ * Wbar ≤ σ ^ 2
  zeta_ge : Λ + ω ≤ ζ
  noise_le : (1 + β / (2 - β)) * (2 * (1 + β) * ζ * σ + δ * ζ ^ 2) ≤ nbar
  noise_small : 4 * nbar ≤ Λ * κstar
  gain : 2 * U ^ 2 ≤ Λ * κstar
  violation_small : (4 * β / (2 - β)) * U * ω ≤ (3 / 2 + 4 * β / (2 - β)) * Λ * κstar - U ^ 2
  kstar_le : κstar ≤ κ₀ - (τ₁ + τ₂) - σ
  U_ge : σ + tnorm + (τ₁ + τ₂) ≤ U
  drift_le : 4 * Wbar * δ * ζ ≤ τ₂ * Λ * κstar

variable (c : Control)
variable {b : ι → ℝ} {a₀ ρ : ℝ} {p : ι → E} {R : ι → F →L[ℝ] E} {w : E} {t₀ : F}
  {x : ℕ → State F E} {i : ℕ → ι} {K : ℕ}

lemma Control.gamma_nonneg : 0 ≤ 1 + c.β / (2 - c.β) := by
  have h1 := c.beta_pos; have h2 := c.beta_le
  have h3 : 0 ≤ c.β / (2 - c.β) := div_nonneg h1.le (by linarith)
  linarith

lemma Control.gamma_ge_one : 1 ≤ 1 + c.β / (2 - c.β) := by
  have h1 := c.beta_pos; have h2 := c.beta_le
  have h3 : 0 ≤ c.β / (2 - c.β) := div_nonneg h1.le (by linarith)
  linarith

lemma Control.c_nonneg : 0 ≤ 4 * c.β / (2 - c.β) := by
  have := c.beta_pos; have := c.beta_le
  exact div_nonneg (by linarith) (by linarith)

lemma Control.zeta_nonneg : 0 ≤ c.ζ := by
  linarith [c.zeta_ge, c.lambda_nonneg, c.omega_nonneg]

lemma Control.lambda_kstar_pos : 0 < c.Λ * c.κstar := by
  have := c.gain; have := c.U_pos; nlinarith

structure PhaseTwoState (w : E) (t₀ : F) (x : State F E) (s j : ℕ) : Prop where
  pot : potential c.Λ c.β c.δ w x ≤ c.Wbar - ((j - s : ℕ) : ℝ) * (c.Λ * c.κstar / 4)
  drift : ‖x.t - t₀‖ ≤ c.τ₁ + ((j - s : ℕ) : ℝ) * (c.δ * c.ζ)

omit [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma potential_nonneg (w : E) (x : State F E) : 0 ≤ potential c.Λ c.β c.δ w x := by
  unfold potential
  have h1 := c.gamma_nonneg
  have h2 : 0 ≤ mass x + phi x := by
    unfold mass phi
    have := abs_nonneg (x.a ^ 2 - x.q ^ 2)
    nlinarith [sq_nonneg x.a, sq_nonneg x.q]
  have h3 : 0 < 2 * c.δ := by linarith [c.delta_pos]
  have h4 : 0 ≤ (1 + c.β / (2 - c.β)) * (mass x + phi x) / (2 * c.δ) :=
    div_nonneg (mul_nonneg h1 h2) h3.le
  have h5 : 0 ≤ ‖x.z - c.Λ • w‖ ^ 2 := sq_nonneg _
  linarith

omit [CompleteSpace E] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma PhaseTwoState.count_le {w : E} {t₀ : F} {y : State F E} {s j : ℕ}
    (h : PhaseTwoState c w t₀ y s j) : ((j - s : ℕ) : ℝ) * (c.Λ * c.κstar / 4) ≤ c.Wbar := by
  have := potential_nonneg c w y
  linarith [h.pot]

omit [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma noise_terms_le {β δ ζ σ b : ℝ} {p : E} {y : State F E} (hβ : 0 < β) (hβ1 : β ≤ 1 / 8)
    (hb : |b| ≤ β) (hσ : 0 ≤ σ)
    (ha : |y.a| ≤ σ) (hq : |y.q| ≤ σ) (hε : |noise δ p y| ≤ δ * ζ) :
    noiseMass b δ p y + noisePhi b δ p y ≤ 4 * (1 + β) * (δ * ζ) * σ + 2 * (δ * ζ) ^ 2 := by
  unfold noiseMass noisePhi
  have hb' := abs_le.mp hb
  have hεn : 0 ≤ |noise δ p y| := abs_nonneg _
  have h1 : |y.a + b * y.q| ≤ (1 + β) * σ := by
    calc |y.a + b * y.q| ≤ |y.a| + |b * y.q| := abs_add_le _ _
      _ = |y.a| + |b| * |y.q| := by rw [abs_mul]
      _ ≤ σ + β * σ := by
          have := mul_le_mul hb hq (abs_nonneg _) hβ.le
          linarith
      _ = (1 + β) * σ := by ring
  have hs2 : |y.a + y.q| + |y.a - y.q| ≤ 2 * σ := by
    have ha' := abs_le.mp ha
    have hq' := abs_le.mp hq
    rcases abs_cases (y.a + y.q) with ⟨h3, _⟩ | ⟨h3, _⟩ <;>
      rcases abs_cases (y.a - y.q) with ⟨h4, _⟩ | ⟨h4, _⟩ <;> linarith
  have h2 : |(1 + b) * (y.a + y.q)| + |(1 - b) * (y.a - y.q)| ≤ (1 + β) * (2 * σ) := by
    rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < 1 + b),
      abs_of_pos (by linarith : 0 < 1 - b)]
    have hA : (1 + b) * |y.a + y.q| ≤ (1 + β) * |y.a + y.q| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    have hB : (1 - b) * |y.a - y.q| ≤ (1 + β) * |y.a - y.q| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    have hC := mul_le_mul_of_nonneg_left hs2 (by linarith : 0 ≤ 1 + β)
    linarith
  have e1 : |2 * noise δ p y * (y.a + b * y.q)| = 2 * |noise δ p y| * |y.a + b * y.q| := by
    rw [abs_mul, abs_mul, abs_two]
  have e2 : |noise δ p y ^ 2| = noise δ p y ^ 2 := abs_of_nonneg (sq_nonneg _)
  have hA : |2 * noise δ p y * (y.a + b * y.q) + noise δ p y ^ 2| ≤
      2 * |noise δ p y| * ((1 + β) * σ) + noise δ p y ^ 2 := by
    calc _ ≤ |2 * noise δ p y * (y.a + b * y.q)| + |noise δ p y ^ 2| := abs_add_le _ _
      _ = 2 * |noise δ p y| * |y.a + b * y.q| + noise δ p y ^ 2 := by rw [e1, e2]
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * |noise δ p y|)
          linarith
  have hB : |noise δ p y| * (|(1 + b) * (y.a + y.q)| + |(1 - b) * (y.a - y.q)|) ≤
      |noise δ p y| * ((1 + β) * (2 * σ)) := mul_le_mul_of_nonneg_left h2 hεn
  have hsq : noise δ p y ^ 2 ≤ (δ * ζ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ hεn hε 2
  have hβσ : 0 ≤ (1 + β) * σ := by positivity
  have hlin : |noise δ p y| * ((1 + β) * σ) ≤ (δ * ζ) * ((1 + β) * σ) :=
    mul_le_mul_of_nonneg_right hε hβσ
  linarith [hA, hB, hsq, hlin]

omit [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma potential_bounds {Λ β δ Wbar ω σ ζ : ℝ} {w : E} {y : State F E} (hw : ‖w‖ = 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1 / 8) (hδ : 0 < δ) (hΛ : 0 ≤ Λ) (hω : 0 ≤ ω) (hσ : 0 ≤ σ)
    (hwbar : Wbar ≤ ω ^ 2) (hmass_le : 2 * δ * Wbar ≤ σ ^ 2) (hζ : Λ + ω ≤ ζ)
    (hW : potential Λ β δ w y ≤ Wbar) :
    ‖y.z - Λ • w‖ ≤ ω ∧ ‖y.z‖ ≤ ζ ∧ |y.a| ≤ σ ∧ |y.q| ≤ σ := by
  have hγ0 : 0 ≤ 1 + β / (2 - β) := by
    have : 0 ≤ β / (2 - β) := div_nonneg hβ.le (by linarith)
    linarith
  have hγ : 1 ≤ 1 + β / (2 - β) := by
    have : 0 ≤ β / (2 - β) := div_nonneg hβ.le (by linarith)
    linarith
  have hmp : 0 ≤ mass y + phi y := by
    unfold mass phi
    have := abs_nonneg (y.a ^ 2 - y.q ^ 2)
    nlinarith [sq_nonneg y.a, sq_nonneg y.q]
  unfold potential at hW
  have hQ : ‖y.z - Λ • w‖ ^ 2 ≤ Wbar := by
    have : 0 ≤ (1 + β / (2 - β)) * (mass y + phi y) / (2 * δ) :=
      div_nonneg (mul_nonneg hγ0 hmp) (by linarith)
    linarith
  have hQω : ‖y.z - Λ • w‖ ≤ ω := by
    have h1 : ‖y.z - Λ • w‖ ^ 2 ≤ ω ^ 2 := by linarith
    exact (abs_le_of_sq_le_sq' h1 hω).2
  have hzn : ‖y.z‖ ≤ ζ := by
    have h1 : ‖y.z‖ ≤ ‖y.z - Λ • w‖ + ‖Λ • w‖ := by
      calc ‖y.z‖ = ‖(y.z - Λ • w) + Λ • w‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖Λ • w‖ = Λ := by
      rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_nonneg hΛ]
    linarith
  have hmass : mass y ≤ σ ^ 2 := by
    have h1 : (1 + β / (2 - β)) * (mass y + phi y) / (2 * δ) ≤ Wbar := by
      have := sq_nonneg ‖y.z - Λ • w‖
      linarith
    have h2 : mass y ≤ (1 + β / (2 - β)) * (mass y + phi y) := by
      have hphi0 : 0 ≤ phi y := abs_nonneg _
      have := mul_le_mul_of_nonneg_right hγ hmp
      linarith
    have h3 : (1 + β / (2 - β)) * (mass y + phi y) ≤ 2 * δ * Wbar := by
      rw [div_le_iff₀ (by linarith)] at h1
      linarith
    linarith
  have hsq : Real.sqrt (mass y) ≤ σ := by
    rw [Real.sqrt_le_left hσ]; exact hmass
  refine ⟨hQω, hzn, (abs_a_le_sqrt_mass y).trans hsq, ?_⟩
  have h : |y.q| ≤ Real.sqrt (mass y) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by unfold mass; nlinarith [sq_nonneg y.a])
  exact h.trans hsq

omit [CompleteSpace E] [CompleteSpace F] in
lemma violation_term_le {Λ κstar U β ω b : ℝ} {w p : E} {R : F →L[ℝ] E} {y : State F E}
    (hβ : 0 < β) (hβ1 : β ≤ 1 / 8) (hw : ‖w‖ = 1) (hp : ‖p‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hΛ : 0 ≤ Λ) (hU0 : 0 ≤ U) (hgain : 2 * U ^ 2 ≤ Λ * κstar)
    (hsmall : (4 * β / (2 - β)) * U * ω ≤ (3 / 2 + 4 * β / (2 - β)) * Λ * κstar - U ^ 2)
    (hκ : κstar ≤ ⟪w, R y.t⟫ - |y.a|) (hU : |y.a| + ‖y.t‖ ≤ U) (hQω : ‖y.z - Λ • w‖ ≤ ω) :
    (4 * β / (2 - β)) * violation b p R y ≤ (3 / 2) * Λ * κstar - U ^ 2 := by
  have hc : 0 ≤ 4 * β / (2 - β) := div_nonneg (by linarith) (by linarith)
  unfold violation
  split_ifs
  · have hΔ : κstar ≤ ⟪w, move p R y⟫ :=
      le_trans hκ (move_inner_margin (p := p) (R := R) (x := y) (κ := ⟪w, R y.t⟫) hw hp
        (le_refl _))
    have hUm : ‖move p R y‖ ≤ U := (move_norm_le p R y hp hR).trans hU
    have hv := violation_bound (Λ := Λ) hΔ hUm hΛ
    have h1 : -res p R y ≤ U * ω - Λ * κstar := by
      have : U * ‖y.z - Λ • w‖ ≤ U * ω := mul_le_mul_of_nonneg_left hQω hU0
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hc
    linarith [h2, hsmall]
  · simp only [mul_zero]
    linarith [hgain, sq_nonneg U]

lemma phaseTwo_step (G : Geometry ρ c.β c.κ₀ b p R w t₀) (ht : ‖t₀‖ ≤ c.tnorm)
    (tr : Trajectory b c.δ p R a₀ t₀ x i K) {s j : ℕ} (hj : j < K) (_hsj : s ≤ j)
    (hs : PhaseTwoState c w t₀ (x j) s j) :
    PhaseTwoState c w t₀ (x (j + 1)) s (j + 1) := by
  set y := x j with hy
  have hβ := c.beta_pos
  have hβ1 := c.beta_le
  have hδ := c.delta_pos
  have hγ0 := c.gamma_nonneg
  have hΛκ := c.lambda_kstar_pos
  have hζ := c.zeta_nonneg
  have hσ := c.sigma_nonneg
  have hjs : (0 : ℝ) ≤ ((j - s : ℕ) : ℝ) := Nat.cast_nonneg _
  have hW : potential c.Λ c.β c.δ w y ≤ c.Wbar := by
    have h1 := hs.pot
    have hn : (0 : ℝ) ≤ ((j - s : ℕ) : ℝ) * (c.Λ * c.κstar / 4) := mul_nonneg hjs (by linarith)
    linarith
  obtain ⟨hQω, hzn, ha, hq⟩ := potential_bounds G.wn hβ hβ1 hδ c.lambda_nonneg c.omega_nonneg
    hσ c.wbar_le c.mass_le c.zeta_ge hW
  have hcount := hs.count_le
  have hdrift : ‖y.t - t₀‖ ≤ c.τ₁ + c.τ₂ := by
    have h1 := hs.drift
    have h2 : ((j - s : ℕ) : ℝ) * (c.δ * c.ζ) ≤ c.τ₂ := by
      have h3 : ((j - s : ℕ) : ℝ) ≤ 4 * c.Wbar / (c.Λ * c.κstar) := by
        rw [le_div_iff₀ hΛκ]; linarith
      have h4 : ((j - s : ℕ) : ℝ) * (c.δ * c.ζ) ≤ 4 * c.Wbar / (c.Λ * c.κstar) * (c.δ * c.ζ) :=
        mul_le_mul_of_nonneg_right h3 (mul_nonneg hδ.le hζ)
      have h5 : 4 * c.Wbar / (c.Λ * c.κstar) * (c.δ * c.ζ) ≤ c.τ₂ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hΛκ]
        linarith [c.drift_le]
      linarith
    linarith
  have htn : ‖y.t‖ ≤ c.tnorm + (c.τ₁ + c.τ₂) := by
    have := norm_sub_norm_le y.t t₀
    linarith
  have hU : |y.a| + ‖y.t‖ ≤ c.U := by linarith [c.U_ge]
  have hκ : c.κstar ≤ ⟪w, (R (i j)) y.t⟫ - |y.a| := by
    have h1 := inner_R_shift (R (i j)) y w t₀ G.wn (G.Rn _)
    have h2 := G.margin (i j)
    linarith [c.kstar_le]
  have hmis := tr.mistake j hj
  have hstep := potential_step_state (κstar := c.κstar) (U := c.U) hβ hβ1 (G.bu _) hδ hmis
    G.wn (G.pn _) (G.Rn _) hκ c.lambda_nonneg hU
  have hε : |noise c.δ (p (i j)) y| ≤ c.δ * c.ζ :=
    (noise_abs_le c.δ (p (i j)) y (G.pn _) hδ.le).trans (mul_le_mul_of_nonneg_left hzn hδ.le)
  have hnoise := noise_terms_le hβ hβ1 (G.bu (i j)) hσ ha hq hε
  have hnoise' : (1 + c.β / (2 - c.β)) *
      (noiseMass (b (i j)) c.δ (p (i j)) y + noisePhi (b (i j)) c.δ (p (i j)) y) / (2 * c.δ) ≤
      c.nbar := by
    have h1 := mul_le_mul_of_nonneg_left hnoise hγ0
    have h2 : (1 + c.β / (2 - c.β)) * (4 * (1 + c.β) * (c.δ * c.ζ) * c.σ + 2 * (c.δ * c.ζ) ^ 2) /
        (2 * c.δ) = (1 + c.β / (2 - c.β)) * (2 * (1 + c.β) * c.ζ * c.σ + c.δ * c.ζ ^ 2) := by
      rw [div_eq_iff (by positivity)]
      ring
    calc _ ≤ (1 + c.β / (2 - c.β)) *
          (4 * (1 + c.β) * (c.δ * c.ζ) * c.σ + 2 * (c.δ * c.ζ) ^ 2) / (2 * c.δ) :=
          div_le_div_of_nonneg_right h1 (by linarith)
      _ = _ := h2
      _ ≤ c.nbar := c.noise_le
  have hviol := violation_term_le (b := b (i j)) hβ hβ1 G.wn (G.pn (i j)) (G.Rn (i j))
    c.lambda_nonneg c.U_pos.le c.gain c.violation_small hκ hU hQω
  have hpot : potential c.Λ c.β c.δ w (x (j + 1)) ≤
      potential c.Λ c.β c.δ w y - c.Λ * c.κstar / 4 := by
    rw [tr.update j hj]
    have := c.noise_small
    linarith
  have hcast : ((j + 1 - s : ℕ) : ℝ) = ((j - s : ℕ) : ℝ) + 1 := by
    have : j + 1 - s = (j - s) + 1 := by omega
    rw [this]; push_cast; ring
  refine ⟨?_, ?_⟩
  · have := hs.pot
    rw [hcast]
    linarith
  · have h1 := hs.drift
    have h2 := t_step tr (fun j => ⟨G.pn j, G.Rn j⟩) hδ.le hj
    have h3 : ‖(x (j + 1)).t - t₀‖ ≤ ‖(x (j + 1)).t - y.t‖ + ‖y.t - t₀‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [hcast]
    have h4 : c.δ * ‖y.z‖ ≤ c.δ * c.ζ := mul_le_mul_of_nonneg_left hzn hδ.le
    linarith

lemma phaseTwo_invariant (G : Geometry ρ c.β c.κ₀ b p R w t₀) (ht : ‖t₀‖ ≤ c.tnorm)
    (tr : Trajectory b c.δ p R a₀ t₀ x i K) {s : ℕ} (hs : PhaseTwoState c w t₀ (x s) s s) :
    ∀ j, s ≤ j → j ≤ K → PhaseTwoState c w t₀ (x j) s j := by
  intro j
  induction j with
  | zero =>
    intro hsj _
    have : s = 0 := by omega
    subst this
    exact hs
  | succ n ih =>
    intro hsj hK
    rcases Nat.lt_or_ge n s with hlt | hge
    · have : s = n + 1 := by omega
      subst this
      exact hs
    · exact phaseTwo_step c G ht tr (by omega) hge (ih hge (by omega))

lemma phaseTwo_length (G : Geometry ρ c.β c.κ₀ b p R w t₀) (ht : ‖t₀‖ ≤ c.tnorm)
    (tr : Trajectory b c.δ p R a₀ t₀ x i K) {s : ℕ} (hsK : s ≤ K)
    (hs : PhaseTwoState c w t₀ (x s) s s) :
    ((K - s : ℕ) : ℝ) * (c.Λ * c.κstar / 4) ≤ c.Wbar :=
  (phaseTwo_invariant c G ht tr hs K hsK le_rfl).count_le

end PhaseTwo

section Length

variable (c₁ : KernelPerceptronPhaseOne.Control) (c₂ : Control)
variable {b : ι → ℝ} {a₀ κ₀ : ℝ} {p : ι → E} {R : ι → F →L[ℝ] E} {w : E} {t₀ : F}
  {x : ℕ → State F E} {i : ℕ → ι} {K : ℕ}

theorem length_le (hδ : 0 < c₂.δ)
    (G₁ : Geometry c₁.ρ c₁.β κ₀ b p R w t₀) (G₂ : Geometry c₁.ρ c₂.β c₂.κ₀ b p R w t₀)
    (ht : ‖t₀‖ ≤ c₂.tnorm) {M₁ : ℕ} {τ : ℝ}
    (hε : c₂.δ * c₁.U * (M₁ + 1) ≤ c₁.ε)
    (hUa : Real.sqrt (a₀ ^ 2 / (1 - 3 * c₁.β)) + ‖t₀‖ + τ ≤ c₁.U)
    (hτ : c₂.δ * c₁.U * (M₁ + 1) * (M₁ + 1) ≤ τ)
    (hτ₁ : c₂.δ * c₁.U * (M₁ + 1) * M₁ ≤ c₂.τ₁)
    (hend : (1 - c₁.ρ ^ 2 / 2) ^ M₁ * a₀ ^ 2 < c₁.φ ^ 2)
    (hW : (c₁.U * M₁ + c₂.Λ) ^ 2 +
      (1 + c₂.β / (2 - c₂.β)) * (c₁.φ ^ 2 / (1 - 3 * c₁.β) + c₁.φ ^ 2) / (2 * c₂.δ) ≤ c₂.Wbar)
    (tr : Trajectory b c₂.δ p R a₀ t₀ x i K) :
    (K : ℝ) ≤ M₁ + 4 * c₂.Wbar / (c₂.Λ * c₂.κstar) := by
  have hΛκ := c₂.lambda_kstar_pos
  have hε' : c₂.δ * c₁.U * ((M₁ + 1 : ℕ) : ℝ) ≤ c₁.ε := by push_cast; exact hε
  have hτ' : c₂.δ * c₁.U * ((M₁ + 1 : ℕ) : ℝ) * ((M₁ + 1 : ℕ) : ℝ) ≤ τ := by push_cast; exact hτ
  by_contra hcon
  push Not at hcon
  have hK1 : M₁ < K := by
    have h1 : (M₁ : ℝ) < K := by
      have : (0:ℝ) ≤ 4 * c₂.Wbar / (c₂.Λ * c₂.κstar) :=
        div_nonneg (by linarith [c₂.wbar_nonneg]) hΛκ.le
      linarith
    exact_mod_cast h1
  have hexit : ∃ s, s ≤ M₁ ∧ phi (x s) < c₁.φ ^ 2 := by
    by_contra hno
    push Not at hno
    have hinv := phaseOne_invariant c₁ hδ G₁ (M := M₁ + 1) (τ := τ) hε' hUa hτ' tr M₁ hK1.le
      (by omega) (fun j hj => hno j (by omega))
    have h1 := hinv.phi_le
    have h2 := hno M₁ le_rfl
    linarith
  classical
  let s := Nat.find hexit
  have hs_spec : s ≤ M₁ ∧ phi (x s) < c₁.φ ^ 2 := Nat.find_spec hexit
  have hs_min : ∀ j, j < s → c₁.φ ^ 2 ≤ phi (x j) := by
    intro j hj
    have h := Nat.find_min hexit hj
    have hjM : j ≤ M₁ := by omega
    by_contra hlt
    push Not at hlt
    exact h ⟨hjM, hlt⟩
  have hsK : s ≤ K := hs_spec.1.trans hK1.le
  have hs1 := phaseOne_invariant c₁ hδ G₁ (M := M₁ + 1) (τ := τ) hε' hUa hτ' tr s hsK
    (by omega) hs_min
  have hU0 : 0 ≤ c₁.U := by linarith [c₁.U_ge]
  have hstart : PhaseTwoState c₂ w t₀ (x s) s s := by
    have hbal := hs1.balanced
    have hmass : (1 - 3 * c₁.β) * mass (x s) ≤ phi (x s) := balanced_mass c₁ hbal
    have hone := c₁.one_sub_ge
    have hmass' : mass (x s) ≤ c₁.φ ^ 2 / (1 - 3 * c₁.β) := by
      rw [le_div_iff₀ (by linarith)]; linarith [hs_spec.2]
    have hs' : (s : ℝ) ≤ M₁ := by exact_mod_cast hs_spec.1
    have hz : ‖(x s).z‖ ≤ c₁.U * M₁ := by
      have := hs1.z_le
      have := mul_le_mul_of_nonneg_left hs' hU0
      linarith
    have hQ : ‖(x s).z - c₂.Λ • w‖ ^ 2 ≤ (c₁.U * M₁ + c₂.Λ) ^ 2 := by
      have h1 : ‖(x s).z - c₂.Λ • w‖ ≤ ‖(x s).z‖ + ‖c₂.Λ • w‖ := norm_sub_le _ _
      have h2 : ‖c₂.Λ • w‖ = c₂.Λ := by
        rw [norm_smul, G₂.wn, mul_one, Real.norm_eq_abs, abs_of_nonneg c₂.lambda_nonneg]
      have h3 : ‖(x s).z - c₂.Λ • w‖ ≤ c₁.U * M₁ + c₂.Λ := by linarith
      exact pow_le_pow_left₀ (norm_nonneg _) h3 2
    refine ⟨?_, ?_⟩
    · simp only [Nat.sub_self, Nat.cast_zero, zero_mul, sub_zero]
      unfold potential
      have hγ := c₂.gamma_nonneg
      have hSΦ : mass (x s) + phi (x s) ≤ c₁.φ ^ 2 / (1 - 3 * c₁.β) + c₁.φ ^ 2 := by
        linarith [hs_spec.2]
      have h4 : (1 + c₂.β / (2 - c₂.β)) * (mass (x s) + phi (x s)) / (2 * c₂.δ) ≤
          (1 + c₂.β / (2 - c₂.β)) * (c₁.φ ^ 2 / (1 - 3 * c₁.β) + c₁.φ ^ 2) / (2 * c₂.δ) := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left hSΦ hγ
      linarith
    · simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
      have h1 := hs1.drift
      have hpos : 0 ≤ c₂.δ * c₁.U * ((M₁ + 1 : ℕ) : ℝ) :=
        mul_nonneg (mul_nonneg hδ.le hU0) (Nat.cast_nonneg _)
      have h2 : c₂.δ * c₁.U * ((M₁ + 1 : ℕ) : ℝ) * s ≤ c₂.δ * c₁.U * ((M₁ + 1 : ℕ) : ℝ) * M₁ :=
        mul_le_mul_of_nonneg_left hs' hpos
      have h3 : c₂.δ * c₁.U * ((M₁ + 1 : ℕ) : ℝ) * M₁ ≤ c₂.τ₁ := by push_cast; exact hτ₁
      linarith
  have hlen := phaseTwo_length c₂ G₂ ht tr hsK hstart
  have hKs : ((K - s : ℕ) : ℝ) = (K : ℝ) - s := by
    rw [Nat.cast_sub hsK]
  rw [hKs] at hlen
  have hs' : (s : ℝ) ≤ M₁ := by exact_mod_cast hs_spec.1
  have : (K : ℝ) - s ≤ 4 * c₂.Wbar / (c₂.Λ * c₂.κstar) := by
    rw [le_div_iff₀ hΛκ]; linarith
  linarith

end Length

end LongTails.Proofs.KernelPerceptronTrajectory
