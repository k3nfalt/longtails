import LongTails.Proofs.KnownValueNondualControl
import LongTails.Proofs.NondualMovement

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.KnownValueNondualProgress

open LongTails.Setups.KnownValueNondualGeneralizedConvex
open LongTails.Algorithms.KnownValueNondual
open KnownValueNondualGeometry

lemma cut_movement (p : Public) (c : Control p) (x z z' grad : Point p) (value slack : ℝ)
    (hmem : z' - p.x0 ∈ rootCut p c x value grad)
    (hcouple : ⟪grad, x - z⟫ ≤ slack) :
    value - p.fstar + (if c.warm then warmScale p / (2 * p.L1) * ‖grad‖ else 0) - slack ≤
      ‖grad‖ * ‖z - z'‖ := by
  have hcut := hmem.2
  have he : p.x0 + (z' - p.x0) - x = z' - x := by module
  change value + ⟪grad, p.x0 + (z' - p.x0) - x⟫ + _ ≤ p.fstar at hcut
  rw [he] at hcut
  have hi : ⟪grad, z - z'⟫ = -⟪grad, z' - x⟫ - ⟪grad, x - z⟫ := by
    rw [← inner_neg_right, ← inner_sub_right]
    congr 1
    module
  have hn := real_inner_le_norm grad (z - z')
  rw [hi] at hn
  linarith

lemma normal_cut_movement (p : Public) (hL0 : 0 < p.L0) (hL1 : 0 < p.L1)
    (c : Control p) (hw : c.warm = false) (x z z' grad : Point p) (value : ℝ)
    (hmem : z' - p.x0 ∈ rootCut p c x value grad)
    (hcouple : ⟪grad, x - z⟫ ≤ ‖grad‖ ^ 2 / (16 * (p.L0 + p.L1 * ‖grad‖)))
    (hfail : c.target < value - 5 * ‖grad‖ ^ 2 / (24 * (p.L0 + p.L1 * ‖grad‖)) - p.fstar) :
    c.target < ‖grad‖ * ‖z - z'‖ := by
  have hm := cut_movement p c x z z' grad value _ hmem hcouple
  simp only [hw, Bool.false_eq_true, ite_false, add_zero] at hm
  have hH : 0 < p.L0 + p.L1 * ‖grad‖ := by positivity
  have hslack : ‖grad‖ ^ 2 / (16 * (p.L0 + p.L1 * ‖grad‖)) ≤
      5 * ‖grad‖ ^ 2 / (24 * (p.L0 + p.L1 * ‖grad‖)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg ‖grad‖]
  linarith

lemma warm_cut_movement (p : Public) (hL0 : 0 < p.L0) (hL1 : 0 < p.L1)
    (c : Control p) (hw : c.warm = true) (x z z' grad : Point p) (value : ℝ)
    (hmem : z' - p.x0 ∈ rootCut p c x value grad)
    (hcouple : ⟪grad, x - z⟫ ≤ ‖grad‖ ^ 2 / (16 * (p.L0 + p.L1 * ‖grad‖)))
    (hval : p.fstar ≤ value) (hgrad : 0 < ‖grad‖) :
    7 * warmScale p / (16 * p.L1) ≤ ‖z - z'‖ := by
  have hm := cut_movement p c x z z' grad value _ hmem hcouple
  simp only [hw, ite_true] at hm
  have hH : 0 < p.L0 + p.L1 * ‖grad‖ := by positivity
  have hh := warmScale_one_le p
  have hslack : ‖grad‖ ^ 2 / (16 * (p.L0 + p.L1 * ‖grad‖)) ≤
      warmScale p * ‖grad‖ / (16 * p.L1) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (mul_nonneg hL1.le (sq_nonneg ‖grad‖)),
      mul_nonneg (show 0 ≤ warmScale p by linarith) (mul_nonneg hL0.le hgrad.le)]
  have he : warmScale p / (2 * p.L1) * ‖grad‖ - warmScale p * ‖grad‖ / (16 * p.L1) =
      ‖grad‖ * (7 * warmScale p / (16 * p.L1)) := by ring
  apply (mul_le_mul_iff_right₀ hgrad).mp
  linarith

lemma low_phase_count {ι : Type*} (s : Finset ι) (G M : ι → ℝ) {Γ C : ℝ}
    (hΓ : 0 < Γ) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hstep : ∀ i ∈ s, Γ ≤ G i * M i) (henergy : (∑ i ∈ s, G i ^ 2) ≤ C * Γ) :
    (s.card : ℝ) ^ 3 * Γ ≤ C * (∑ i ∈ s, M i) ^ 2 := by
  have h := NondualMovement.weighted_cube_of_nonneg s (fun i => G i ^ 2 / Γ ^ 2) M (fun _ => 1)
    (fun i _ => by positivity) hM (fun _ _ => by norm_num) (by
      intro i hi
      have hs := pow_le_pow_left₀ hΓ.le (hstep i hi) 2
      rw [mul_pow] at hs
      have hd : Γ ^ 2 ≤ G i ^ 2 * M i ^ 2 := hs
      have he : G i ^ 2 / Γ ^ 2 * M i ^ 2 = G i ^ 2 * M i ^ 2 / Γ ^ 2 := by ring
      rw [he]
      simpa using (le_div_iff₀ (sq_pos_of_pos hΓ)).mpr (by simpa using hd))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.sum_div] at h
  have hh : (s.card : ℝ) ^ 3 * Γ ^ 2 ≤ (∑ i ∈ s, G i ^ 2) * (∑ i ∈ s, M i) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hΓ)).mp
    simpa only [div_mul_eq_mul_div] using h
  have he := mul_le_mul_of_nonneg_right henergy (sq_nonneg (∑ i ∈ s, M i))
  apply (mul_le_mul_iff_left₀ hΓ).mp
  nlinarith only [hh, he]

lemma high_phase_count {ι : Type*} (s : Finset ι) (G M : ι → ℝ) {Γ C : ℝ}
    (hΓ : 0 < Γ) (hG : ∀ i ∈ s, 0 ≤ G i) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hstep : ∀ i ∈ s, Γ ≤ G i * M i) (henergy : (∑ i ∈ s, G i) ≤ C * Γ) :
    (s.card : ℝ) ^ 2 ≤ C * (∑ i ∈ s, M i) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (f := fun i => G i / Γ) (g := M) (r := fun _ => 1)
    (fun i hi => div_nonneg (hG i hi) hΓ.le) hM (by
      intro i hi
      rw [div_mul_eq_mul_div]
      simpa using (le_div_iff₀ hΓ).mpr (by simpa using hstep i hi))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.sum_div] at h
  exact h.trans (mul_le_mul_of_nonneg_right ((div_le_iff₀ hΓ).mpr henergy)
    (Finset.sum_nonneg hM))

lemma low_descent_energy {L0 L1 G : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1)
    (hG : 0 ≤ G) (hsmall : L1 * G ≤ L0) :
    G ^ 2 ≤ (48 / 5 : ℝ) * L0 * (5 * G ^ 2 / (24 * (L0 + L1 * G))) := by
  have hH : 0 < L0 + L1 * G := by positivity
  have hD : 0 ≤ 5 * G ^ 2 / (24 * (L0 + L1 * G)) := by positivity
  have he : (5 * G ^ 2 / (24 * (L0 + L1 * G))) * (24 * (L0 + L1 * G)) = 5 * G ^ 2 :=
    div_mul_cancel₀ _ (by positivity)
  nlinarith [mul_nonneg hD (sub_nonneg.mpr hsmall)]

lemma high_descent_energy {L0 L1 G : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1)
    (hlarge : L0 ≤ L1 * G) :
    G ≤ (48 / 5 : ℝ) * L1 * (5 * G ^ 2 / (24 * (L0 + L1 * G))) := by
  have hGp : 0 < G := by nlinarith
  have hH : 0 < L0 + L1 * G := by positivity
  have hD : 0 ≤ 5 * G ^ 2 / (24 * (L0 + L1 * G)) := by positivity
  have he : (5 * G ^ 2 / (24 * (L0 + L1 * G))) * (24 * (L0 + L1 * G)) = 5 * G ^ 2 :=
    div_mul_cancel₀ _ (by positivity)
  apply (mul_le_mul_iff_left₀ hGp).mp
  nlinarith [mul_nonneg hD (sub_nonneg.mpr hlarge)]

lemma squared_target_potential_jump {a b gap : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hba : b ≤ a) (hab : a ≤ 2 * b) (hgap : gap ≤ a) :
    gap / b ^ 2 - gap / a ^ 2 ≤ 3 * (1 / b - 1 / a) := by
  have hc : 0 ≤ 1 / b ^ 2 - 1 / a ^ 2 := by
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (sq_pos_of_pos hb) (sq_le_sq₀ hb.le ha.le |>.mpr hba)
  have hmul := mul_le_mul_of_nonneg_right hgap hc
  have he : a * (1 / b ^ 2 - 1 / a ^ 2) = (a / b + 1) * (1 / b - 1 / a) := by
    field_simp
    ring
  have hc' : 0 ≤ 1 / b - 1 / a := sub_nonneg.mpr (one_div_le_one_div_of_le hb hba)
  have hr : a / b + 1 ≤ 3 := by
    have hh := (div_le_iff₀ hb).mpr hab
    linarith
  have hmul' := mul_le_mul_of_nonneg_right hr hc'
  rw [he] at hmul
  calc
    _ = gap * (1 / b ^ 2 - 1 / a ^ 2) := by ring
    _ ≤ _ := hmul.trans hmul'

lemma target_potential_jump {a b gap : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hba : b ≤ a) (hab : a ≤ 2 * b) (hgap : gap ≤ a) :
    gap / b - gap / a ≤ 1 := by
  have hc : 0 ≤ 1 / b - 1 / a := sub_nonneg.mpr (one_div_le_one_div_of_le hb hba)
  have hmul := mul_le_mul_of_nonneg_right hgap hc
  have he : a * (1 / b - 1 / a) = a / b - 1 := by field_simp
  rw [he] at hmul
  have hr : a / b ≤ 2 := (div_le_iff₀ hb).mpr hab
  calc
    _ = gap * (1 / b - 1 / a) := by ring
    _ ≤ 1 := by linarith

end LongTails.Proofs.KnownValueNondualProgress
