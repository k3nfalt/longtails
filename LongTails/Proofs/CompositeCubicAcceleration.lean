import LongTails.Algorithms.CompositeCubicAcceleration
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

namespace LongTails.Proofs.CompositeCubicAcceleration

open LongTails.Algorithms.CompositeCubicAcceleration
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma trialWeight_pos {μ A : ℝ} (hμ : 0 < μ) (hA : 0 ≤ A) :
    0 < trialWeight μ A := by
  unfold trialWeight
  positivity

lemma trialWeight_identity {μ A : ℝ} (hμ : 0 < μ) (hA : 0 ≤ A) :
    μ * trialWeight μ A ^ 2 = A + trialWeight μ A := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 + 4 * μ * A)
  unfold trialWeight
  field_simp
  simp only [mul_comm 4 μ] at hs
  nlinarith

lemma norm_momentum (v x s : E) (a : ℝ) :
    ‖v - a • s - x‖ ^ 2 / 2 - ‖v - x‖ ^ 2 / 2 =
      -a * ⟪s, v - x⟫ + a ^ 2 * ‖s‖ ^ 2 / 2 := by
  have he : v - a • s - x = (v - x) - a • s := by abel
  rw [he, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, inner_smul_right,
    real_inner_comm (v - x) s]
  nlinarith [sq_abs a]

lemma residual_dissipation {s d : E} {lam σ c b : ℝ}
    (hlam : 0 < lam) (hb : 0 ≤ b) (hcb : c * lam ≤ b)
    (hr : ‖s + lam • d‖ ^ 2 ≤ σ ^ 2 * lam ^ 2 * ‖d‖ ^ 2) :
    b * ⟪s, d⟫ + c * ‖s‖ ^ 2 / 2 ≤
      -(1 - σ ^ 2) * b * lam * ‖d‖ ^ 2 / 2 := by
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos hlam,
    inner_smul_right] at hr
  have h₁ := mul_le_mul_of_nonneg_left hr hb
  have h₂ := mul_le_mul_of_nonneg_right hcb (sq_nonneg ‖s‖)
  have hh : lam * (b * ⟪s, d⟫ + c * ‖s‖ ^ 2 / 2) ≤
      lam * (-(1 - σ ^ 2) * b * lam * ‖d‖ ^ 2 / 2) := by
    nlinarith only [h₁, h₂]
  exact (mul_le_mul_iff_right₀ hlam).mp hh

lemma damped_potential {x v y z xstar s : E}
    {A a T β Anew lam σ Fx Fz Fstar Fnew : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hβ : 0 ≤ β) (hT : T = A + a)
    (hweight : Anew = (1 - β) * A + β * T)
    (hcenter : T • y = A • x + a • v)
    (hconvex : Anew * Fnew ≤ (1 - β) * A * Fx + β * T * Fz)
    (hsx : Fz - Fx ≤ ⟪s, z - x⟫)
    (hsstar : Fz - Fstar ≤ ⟪s, z - xstar⟫)
    (hlam : 0 < lam) (hstep : (β * a) ^ 2 * lam ≤ β * T)
    (hr : ‖s + lam • (z - y)‖ ^ 2 ≤ σ ^ 2 * lam ^ 2 * ‖z - y‖ ^ 2) :
    Anew * (Fnew - Fstar) + ‖v - (β * a) • s - xstar‖ ^ 2 / 2 +
      (1 - σ ^ 2) * β * T * lam * ‖z - y‖ ^ 2 / 2 ≤
      A * (Fx - Fstar) + ‖v - xstar‖ ^ 2 / 2 := by
  have hbalance : A • (z - x) + a • (z - xstar) =
      T • (z - y) + a • (v - xstar) := by
    calc
      _ = (A + a) • z - (A • x + a • v) + a • (v - xstar) := by module
      _ = _ := by rw [← hT, ← hcenter]; module
  have hi := congrArg (fun w => ⟪s, w⟫) hbalance
  simp only [inner_add_right, inner_smul_right] at hi
  have hx := mul_le_mul_of_nonneg_left hsx hA
  have hs := mul_le_mul_of_nonneg_left hsstar ha
  have hbase : T * (Fz - Fstar) - A * (Fx - Fstar) ≤
      T * ⟪s, z - y⟫ + a * ⟪s, v - xstar⟫ := by
    rw [hT] at hi ⊢
    nlinarith only [hx, hs, hi]
  have hmul := mul_le_mul_of_nonneg_left hbase hβ
  have hm := norm_momentum v xstar s (β * a)
  have ht0 : 0 ≤ β * T := mul_nonneg hβ (by linarith)
  have hd := residual_dissipation hlam ht0 hstep hr
  rw [hweight] at hconvex ⊢
  nlinarith only [hmul, hm, hd, hconvex]

lemma damping_properties {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 < lam) :
    0 < min 1 (μ / lam) ∧ min 1 (μ / lam) ≤ 1 ∧
      min 1 (μ / lam) * lam = min μ lam := by
  refine ⟨lt_min (by norm_num) (div_pos hμ hlam), min_le_left _ _, ?_⟩
  by_cases h : lam ≤ μ
  · rw [min_eq_left ((le_div_iff₀ hlam).mpr (by simpa using h)), min_eq_right h]
    ring
  · have hm : μ / lam ≤ 1 := (div_le_one hlam).mpr (le_of_not_ge h)
    rw [min_eq_right hm, min_eq_left (le_of_not_ge h), div_mul_cancel₀ _ hlam.ne']

lemma center_identity (state : State E) {μ : ℝ} (hμ : 0 < μ) (hA : 0 ≤ state.weight) :
    (state.weight + trialWeight μ state.weight) • center E μ state =
      state.weight • state.point + trialWeight μ state.weight • state.momentum := by
  have ht : state.weight + trialWeight μ state.weight ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos hA (trialWeight_pos hμ hA))
  simp only [center, smul_smul, mul_inv_cancel₀ ht, one_smul]

lemma damped_step_bound {μ lam A : ℝ} (hμ : 0 < μ) (hlam : 0 < lam) (hA : 0 ≤ A) :
    (min 1 (μ / lam) * trialWeight μ A) ^ 2 * lam ≤
      min 1 (μ / lam) * (A + trialWeight μ A) := by
  let β := min 1 (μ / lam)
  have hb := damping_properties hμ hlam
  have hm : β * lam ≤ μ := by dsimp [β]; rw [hb.2.2]; exact min_le_left _ _
  have hp : 0 ≤ β * trialWeight μ A ^ 2 := mul_nonneg hb.1.le (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_left hm hp
  have hi := trialWeight_identity hμ hA
  change (β * trialWeight μ A) ^ 2 * lam ≤ β * (A + trialWeight μ A)
  calc
    _ ≤ β * (μ * trialWeight μ A ^ 2) := by nlinarith only [h]
    _ = _ := by rw [hi]

lemma convex_mixture {F : E → ℝ} {C : Set E} (hF : ConvexOn ℝ C F)
    {x z : E} (hx : x ∈ C) (hz : z ∈ C) {b c : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : 0 < b + c) :
    (b + c)⁻¹ • (b • x + c • z) ∈ C ∧
      (b + c) * F ((b + c)⁻¹ • (b • x + c • z)) ≤ b * F x + c * F z := by
  have hw : b / (b + c) + c / (b + c) = 1 := by field_simp
  have he : (b + c)⁻¹ • (b • x + c • z) =
      (b / (b + c)) • x + (c / (b + c)) • z := by
    simp only [smul_add, smul_smul, div_eq_mul_inv, mul_comm]
  rw [he]
  refine ⟨hF.1 hx hz (div_nonneg hb hs.le) (div_nonneg hc hs.le) hw, ?_⟩
  have h := hF.2 hx hz (div_nonneg hb hs.le) (div_nonneg hc hs.le) hw
  simp only [smul_eq_mul] at h
  have hh := mul_le_mul_of_nonneg_left h hs.le
  have heq : (b + c) * (b / (b + c) * F x + c / (b + c) * F z) =
      b * F x + c * F z := by field_simp
  rwa [heq] at hh

lemma trial_weight_upper {μ A b : ℝ} (hμ : 0 < μ) (hA : 0 ≤ A)
    (hAb : A ≤ 2 * b) (hμb : 1 ≤ μ * b) : trialWeight μ A ≤ 2 * b := by
  have ha := trialWeight_pos hμ hA
  have hid := trialWeight_identity hμ hA
  by_contra h
  have hlt : 2 * b < trialWeight μ A := lt_of_not_ge h
  have hm := mul_lt_mul_of_pos_left hlt hμ
  have hma : 2 < μ * trialWeight μ A := by nlinarith only [hm, hμb]
  have hp := mul_pos (sub_pos.mpr hma) ha
  nlinarith only [hid, hp, hAb, hlt]

lemma low_bucket_trial_upper {μ A : ℝ} (hμ : 0 < μ) (hA : 0 ≤ A) (hbound : A ≤ μ⁻¹) :
    A + trialWeight μ A ≤ 3 / μ := by
  have hi := inv_pos.mpr hμ
  have hm : 1 ≤ μ * μ⁻¹ := by rw [mul_inv_cancel₀ hμ.ne']
  have ht := trial_weight_upper hμ hA (by linarith : A ≤ 2 * μ⁻¹) hm
  rw [div_eq_mul_inv]
  linarith

lemma high_bucket_trial_upper {μ A b : ℝ} (hμ : 0 < μ) (hA : 0 ≤ A)
    (hAb : A ≤ 2 * b) (hμb : 1 ≤ μ * b) :
    A + trialWeight μ A ≤ 4 * b := by
  have ht := trial_weight_upper hμ hA hAb hμb
  linarith

lemma success_sqrt_progress {μ A : ℝ} (hμ : 0 < μ) (hA : 0 ≤ A) :
    1 / (2 * Real.sqrt μ) ≤ Real.sqrt (A + trialWeight μ A) - Real.sqrt A := by
  have ha := trialWeight_pos hμ hA
  have hid := trialWeight_identity hμ hA
  have hT : 0 ≤ A + trialWeight μ A := by linarith
  have hroot : Real.sqrt μ * trialWeight μ A = Real.sqrt (A + trialWeight μ A) := by
    apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) ha.le) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hμ.le, Real.sq_sqrt hT]
    exact hid
  have hsq := sq_nonneg (Real.sqrt (A + trialWeight μ A) - Real.sqrt A)
  have hTA := Real.sq_sqrt hT
  have hAA := Real.sq_sqrt hA
  have h : trialWeight μ A ≤ 2 * Real.sqrt (A + trialWeight μ A) *
      (Real.sqrt (A + trialWeight μ A) - Real.sqrt A) := by nlinarith only [hsq, hTA, hAA]
  rw [← hroot] at h
  have hc : 1 ≤ 2 * Real.sqrt μ * (Real.sqrt (A + trialWeight μ A) - Real.sqrt A) := by
    rw [← hroot]
    apply le_of_mul_le_mul_left (a := trialWeight μ A) ?_ ha
    nlinarith only [h]
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.sqrt_pos.mpr hμ))).mpr
  nlinarith only [hc]

lemma bucket_count_cube {ι : Type*} (s : Finset ι) (a r : ι → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (ha : ∀ i ∈ s, 0 ≤ a i) (hr : ∀ i ∈ s, 0 ≤ r i)
    (hprod : ∀ i ∈ s, c ≤ a i * r i) :
    (s.card : ℝ) ^ 3 * c ^ 2 ≤ (∑ i ∈ s, a i) ^ 2 * (∑ i ∈ s, r i ^ 2) := by
  have h₁ := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s ha hr
    (r := fun _ => Real.sqrt c) (fun i hi => by rw [Real.sq_sqrt hc]; exact hprod i hi)
  have h₁' : (s.card : ℝ) ^ 2 * c ≤ (∑ i ∈ s, a i) * (∑ i ∈ s, r i) := by
    simpa [Finset.sum_const, nsmul_eq_mul, mul_pow, Real.sq_sqrt hc] using h₁
  have h₂ := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) r
  have h₂' : (∑ i ∈ s, r i) ^ 2 ≤ (s.card : ℝ) * (∑ i ∈ s, r i ^ 2) := by
    simpa using h₂
  have h₃ := pow_le_pow_left₀ (mul_nonneg (sq_nonneg (s.card : ℝ)) hc) h₁' 2
  have h₄ := mul_le_mul_of_nonneg_left h₂' (sq_nonneg (∑ i ∈ s, a i))
  by_cases hs : s.card = 0
  · simp only [hs, Nat.cast_zero, zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_mul]
    positivity
  · have hn : (0 : ℝ) < s.card := by exact_mod_cast (Nat.pos_of_ne_zero hs)
    apply le_of_mul_le_mul_left (a := (s.card : ℝ)) ?_ hn
    nlinarith only [h₃, h₄]

lemma sum_selected_increments {A : ℕ → ℝ} (hA : Monotone A) (hA0 : 0 ≤ A 0)
    (s : Finset ℕ) {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ k ∈ s, A (k + 1) ≤ B) :
    (∑ k ∈ s, (A (k + 1) - A k)) ≤ B := by
  by_cases hs : s.Nonempty
  · let j := s.max' hs
    have hsub : s ⊆ Finset.range (j + 1) := by
      intro k hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' s k hk))
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => sub_nonneg.mpr (hA (Nat.le_succ k)))
    rw [Finset.sum_range_sub] at hsum
    have hj := hbound j (Finset.max'_mem s hs)
    linarith
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simpa [he] using hB

lemma dyadic_cover {t : ℝ} (ht : 1 ≤ t) (L : ℕ) (hupper : t < (2 : ℝ) ^ (L + 1)) :
    ∃ j ≤ L, (2 : ℝ) ^ j ≤ t ∧ t < (2 : ℝ) ^ (j + 1) := by
  induction L with
  | zero => exact ⟨0, le_rfl, by simpa using ht, hupper⟩
  | succ L ih =>
    by_cases h : t < (2 : ℝ) ^ (L + 1)
    · obtain ⟨j, hj, hlo, hhi⟩ := ih h
      exact ⟨j, hj.trans (Nat.le_succ L), hlo, hhi⟩
    · exact ⟨L + 1, le_rfl, le_of_not_gt h, hupper⟩

lemma trialWeight_lower {μ A : ℝ} (hμ : 0 < μ) (hA : 0 ≤ A) :
    μ⁻¹ ≤ trialWeight μ A := by
  have hs : 1 ≤ Real.sqrt (1 + 4 * μ * A) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [mul_nonneg hμ.le hA]
  dsimp only [trialWeight]
  apply (le_div_iff₀ (by positivity : 0 < 2 * μ)).mpr
  have he : μ⁻¹ * (2 * μ) = 2 := by field_simp
  rw [he]
  linarith

lemma advance_certificate {F : E → ℝ} {C : Set E} (hF : ConvexOn ℝ C F)
    (state : State E) {z s xstar : E} {μ γ : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hA : 0 ≤ state.weight)
    (hx : state.point ∈ C) (hz : z ∈ C) (hstar : xstar ∈ C)
    (hne : z ≠ center E μ state)
    (hsub : ∀ u ∈ C, F z + ⟪s, u - z⟫ ≤ F u)
    (hr : ‖s + (γ * ‖z - center E μ state‖) • (z - center E μ state)‖ ≤
      γ * ‖z - center E μ state‖ ^ 2 / 32) :
    let next := advance E μ γ state z s
    next.point ∈ C ∧ state.weight < next.weight ∧
      next.weight * (F next.point - F xstar) + ‖next.momentum - xstar‖ ^ 2 / 2 +
        (1 - (1 / 32 : ℝ) ^ 2) * (state.weight + trialWeight μ state.weight) *
          min μ (γ * ‖z - center E μ state‖) * ‖z - center E μ state‖ ^ 2 / 2 ≤
      state.weight * (F state.point - F xstar) + ‖state.momentum - xstar‖ ^ 2 / 2 := by
  let a := trialWeight μ state.weight
  let T := state.weight + a
  let lam := γ * ‖z - center E μ state‖
  let β := min 1 (μ / lam)
  have ha : 0 < a := trialWeight_pos hμ hA
  have hT : 0 < T := add_pos_of_nonneg_of_pos hA ha
  have hlam : 0 < lam := mul_pos hγ (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hb := damping_properties hμ hlam
  have hweight : (1 - β) * state.weight + β * T = state.weight + β * a := by dsimp only [T]; ring
  have hnext : 0 < state.weight + β * a := add_pos_of_nonneg_of_pos hA (mul_pos hb.1 ha)
  have hmix := convex_mixture hF hx hz (mul_nonneg (sub_nonneg.mpr hb.2.1) hA)
    (mul_nonneg hb.1.le hT.le) (by rwa [hweight])
  rw [hweight] at hmix
  have hsx : F z - F state.point ≤ ⟪s, z - state.point⟫ := by
    have h := hsub state.point hx
    rw [show state.point - z = -(z - state.point) by abel, inner_neg_right] at h
    linarith
  have hss : F z - F xstar ≤ ⟪s, z - xstar⟫ := by
    have h := hsub xstar hstar
    rw [show xstar - z = -(z - xstar) by abel, inner_neg_right] at h
    linarith
  have hrsq : ‖s + lam • (z - center E μ state)‖ ^ 2 ≤
      (1 / 32 : ℝ) ^ 2 * lam ^ 2 * ‖z - center E μ state‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hr 2
    convert h using 1
    dsimp only [lam]
    ring
  have hpot := damped_potential hA ha.le hb.1.le rfl hweight.symm
    (center_identity state hμ hA) hmix.2 hsx hss hlam (damped_step_bound hμ hlam hA) hrsq
  change (advance E μ γ state z s).point ∈ C ∧ _
  refine ⟨hmix.1, ?_, ?_⟩
  · change state.weight < state.weight + β * a
    exact lt_add_of_pos_right _ (mul_pos hb.1 ha)
  · have he : β * lam = min μ lam := hb.2.2
    convert hpot using 1
    dsimp only [advance, damping, a, T, β, lam] at *
    rw [← he]
    ring

lemma bucket_card_bound {ι : Type*} (s : Finset ι) (a r : ι → ℝ) {c U V v : ℝ}
    (hc : 0 < c) (hv : 0 ≤ v) (ha : ∀ i ∈ s, 0 ≤ a i) (hr : ∀ i ∈ s, 0 ≤ r i)
    (hprod : ∀ i ∈ s, c ≤ a i * r i)
    (hU : (∑ i ∈ s, a i) ≤ U) (hV : (∑ i ∈ s, r i ^ 2) ≤ V)
    (hscale : U ^ 2 * V ≤ (4 * v) ^ 3 * c ^ 2) : (s.card : ℝ) ≤ 4 * v := by
  have h := bucket_count_cube s a r hc.le ha hr hprod
  have ha0 : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg ha
  have hsq := pow_le_pow_left₀ ha0 hU 2
  have hmul := mul_le_mul hsq hV (Finset.sum_nonneg (fun i _ => sq_nonneg (r i))) (sq_nonneg U)
  have hp : (s.card : ℝ) ^ 3 * c ^ 2 ≤ (4 * v) ^ 3 * c ^ 2 := h.trans (hmul.trans hscale)
  have hp' : (s.card : ℝ) ^ 3 ≤ (4 * v) ^ 3 := (mul_le_mul_iff_left₀ (sq_pos_of_pos hc)).mp hp
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp hp'

lemma low_bucket_scale {μ γ R v : ℝ} (hμ : 0 < μ) (hγ : 0 < γ)
    (hid : μ ^ 2 * v ^ 3 = γ ^ 2 * R ^ 2) :
    (3 / μ) ^ 2 * (2 * R ^ 2) ≤ (4 * v) ^ 3 * (γ⁻¹) ^ 2 := by
  apply (mul_le_mul_iff_left₀ (show 0 < μ ^ 2 * γ ^ 2 by positivity)).mp
  field_simp
  nlinarith only [hid, mul_nonneg (sq_nonneg γ) (sq_nonneg R)]

lemma high_bucket_scale {μ γ R v b : ℝ} (hμ : 0 < μ) (hγ : 0 < γ) (hb : 0 < b)
    (hid : μ ^ 2 * v ^ 3 = γ ^ 2 * R ^ 2) :
    (4 * b) ^ 2 * (2 * R ^ 2 / (μ * b)) ≤ (4 * v) ^ 3 * (Real.sqrt (μ * b) / γ) ^ 2 := by
  rw [div_pow, Real.sq_sqrt (mul_nonneg hμ.le hb.le)]
  apply (mul_le_mul_iff_left₀ (show 0 < μ * γ ^ 2 by positivity)).mp
  field_simp
  nlinarith only [hid, mul_nonneg (sq_nonneg γ) (sq_nonneg R)]

lemma failure_product {μ γ A r : ℝ} (hμ : 0 < μ) (hγ : 0 < γ)
    (hr : 0 < r) (hfail : μ < γ * r) :
    γ * (min 1 (μ / (γ * r)) * trialWeight μ A * r) = μ * trialWeight μ A := by
  rw [min_eq_right (le_of_lt ((div_lt_one (mul_pos hγ hr)).mpr hfail))]
  field_simp

lemma low_failure_product {μ γ A r : ℝ} (hμ : 0 < μ) (hγ : 0 < γ) (hA : 0 ≤ A)
    (hr : 0 < r) (hfail : μ < γ * r) :
    γ⁻¹ ≤ (min 1 (μ / (γ * r)) * trialWeight μ A) * r := by
  have he := failure_product (A := A) hμ hγ hr hfail
  have hlo := mul_le_mul_of_nonneg_left (trialWeight_lower hμ hA) hμ.le
  rw [mul_inv_cancel₀ hμ.ne'] at hlo
  apply (mul_le_mul_iff_right₀ hγ).mp
  rw [mul_inv_cancel₀ hγ.ne', he]
  exact hlo

lemma high_failure_product {μ γ A r b : ℝ} (hμ : 0 < μ) (hγ : 0 < γ) (hA : 0 ≤ A)
    (hr : 0 < r) (hb : 0 ≤ b) (hbA : b ≤ A) (hfail : μ < γ * r) :
    Real.sqrt (μ * b) / γ ≤ (min 1 (μ / (γ * r)) * trialWeight μ A) * r := by
  have he := failure_product (A := A) hμ hγ hr hfail
  have hid := trialWeight_identity hμ hA
  have ha := trialWeight_pos hμ hA
  have hs := Real.sq_sqrt (mul_nonneg hμ.le hb)
  have hsq : (μ * trialWeight μ A) ^ 2 = μ * (A + trialWeight μ A) := by nlinarith only [congrArg (fun t => μ * t) hid]
  have hlo := mul_le_mul_of_nonneg_left hbA hμ.le
  have hpos : 0 ≤ μ * trialWeight μ A := mul_nonneg hμ.le ha.le
  have hroot : Real.sqrt (μ * b) ≤ μ * trialWeight μ A := by
    nlinarith only [hs, hsq, hlo, mul_nonneg hμ.le ha.le, hpos, Real.sqrt_nonneg (μ * b)]
  apply (div_le_iff₀ hγ).mpr
  nlinarith only [he, hroot]

lemma low_failure_card (s : Finset ℕ) (A r : ℕ → ℝ) {μ γ R v : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hv : 0 ≤ v) (hA : Monotone A) (hA0 : 0 ≤ A 0)
    (hr : ∀ k ∈ s, 0 < r k) (hfail : ∀ k ∈ s, μ < γ * r k)
    (hsmall : ∀ k ∈ s, A k ≤ μ⁻¹)
    (hrec : ∀ k ∈ s, A (k + 1) = A k + min 1 (μ / (γ * r k)) * trialWeight μ (A k))
    (hV : (∑ k ∈ s, r k ^ 2) ≤ 2 * R ^ 2)
    (hid : μ ^ 2 * v ^ 3 = γ ^ 2 * R ^ 2) : (s.card : ℝ) ≤ 4 * v := by
  have hpos (k : ℕ) : 0 ≤ A k := hA0.trans (hA (Nat.zero_le k))
  apply bucket_card_bound s (fun k => A (k + 1) - A k) r (inv_pos.mpr hγ) hv
    (fun k _ => sub_nonneg.mpr (hA (Nat.le_succ k))) (fun k hk => (hr k hk).le) ?_ ?_ hV
    (low_bucket_scale hμ hγ hid)
  · intro k hk
    rw [hrec k hk, add_sub_cancel_left]
    exact low_failure_product hμ hγ (hpos k) (hr k hk) (hfail k hk)
  · apply sum_selected_increments hA hA0 s (by positivity)
    intro k hk
    have hb := (damping_properties hμ (mul_pos hγ (hr k hk))).2.1
    have ht := low_bucket_trial_upper hμ (hpos k) (hsmall k hk)
    have ha := trialWeight_pos hμ (hpos k)
    rw [hrec k hk]
    nlinarith only [hb, ht, ha]

lemma high_failure_card (s : Finset ℕ) (A r : ℕ → ℝ) {μ γ R v b : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hv : 0 ≤ v) (hb : 0 < b) (hμb : 1 ≤ μ * b)
    (hA : Monotone A) (hA0 : 0 ≤ A 0)
    (hr : ∀ k ∈ s, 0 < r k) (hfail : ∀ k ∈ s, μ < γ * r k)
    (hlow : ∀ k ∈ s, b ≤ A k) (hhigh : ∀ k ∈ s, A k ≤ 2 * b)
    (hrec : ∀ k ∈ s, A (k + 1) = A k + min 1 (μ / (γ * r k)) * trialWeight μ (A k))
    (hV : (∑ k ∈ s, r k ^ 2) ≤ 2 * R ^ 2 / (μ * b))
    (hid : μ ^ 2 * v ^ 3 = γ ^ 2 * R ^ 2) : (s.card : ℝ) ≤ 4 * v := by
  have hpos (k : ℕ) : 0 ≤ A k := hA0.trans (hA (Nat.zero_le k))
  apply bucket_card_bound s (fun k => A (k + 1) - A k) r
    (div_pos (Real.sqrt_pos_of_pos (mul_pos hμ hb)) hγ) hv
    (fun k _ => sub_nonneg.mpr (hA (Nat.le_succ k))) (fun k hk => (hr k hk).le) ?_ ?_ hV
    (high_bucket_scale hμ hγ hb hid)
  · intro k hk
    rw [hrec k hk, add_sub_cancel_left]
    exact high_failure_product hμ hγ (hpos k) (hr k hk) hb.le (hlow k hk) (hfail k hk)
  · apply sum_selected_increments hA hA0 s (by positivity)
    intro k hk
    have hβ := (damping_properties hμ (mul_pos hγ (hr k hk))).2.1
    have ht := high_bucket_trial_upper hμ (hpos k) (hhigh k hk) hμb
    have ha := trialWeight_pos hμ (hpos k)
    rw [hrec k hk]
    nlinarith only [hβ, ht, ha]

lemma selected_radii_bound (s t : Finset ℕ) (w r : ℕ → ℝ) {c D : ℝ}
    (hsub : s ⊆ t) (hc : 0 < c) (hw : ∀ k ∈ t, 0 ≤ w k)
    (hlow : ∀ k ∈ s, c ≤ w k) (hsum : (∑ k ∈ t, w k * r k ^ 2) ≤ D) :
    (∑ k ∈ s, r k ^ 2) ≤ D / c := by
  apply (le_div_iff₀ hc).mpr
  have h1 := Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_right (hlow k hk) (sq_nonneg (r k)))
  have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun k hk _ => mul_nonneg (hw k hk) (sq_nonneg (r k)))
  rw [← Finset.mul_sum] at h1
  nlinarith only [h1, h2, hsum]

lemma success_card (s : Finset ℕ) (A : ℕ → ℝ) (N : ℕ) {μ X v : ℝ}
    (hμ : 0 < μ) (hv : 0 ≤ v) (hA : Monotone A) (hA0 : 0 ≤ A 0)
    (hs : s ⊆ Finset.range N) (hAN : A N ≤ X)
    (hstep : ∀ k ∈ s, A (k + 1) = A k + trialWeight μ (A k))
    (hid : μ * X = v ^ 2) : (s.card : ℝ) ≤ 2 * v := by
  have hpos (k : ℕ) : 0 ≤ A k := hA0.trans (hA (Nat.zero_le k))
  have hmono : Monotone (fun k => Real.sqrt (A k)) := fun _ _ hij => Real.sqrt_le_sqrt (hA hij)
  have hsum := sum_selected_increments hmono (Real.sqrt_nonneg _) s (Real.sqrt_nonneg X)
    (fun k hk => Real.sqrt_le_sqrt ((hA (Nat.succ_le_of_lt (Finset.mem_range.mp (hs hk)))).trans hAN))
  have hlo : ∀ k ∈ s, 1 / (2 * Real.sqrt μ) ≤ Real.sqrt (A (k + 1)) - Real.sqrt (A k) := by
    intro k hk
    rw [hstep k hk]
    exact success_sqrt_progress hμ (hpos k)
  have hsumlo := Finset.sum_le_sum hlo
  simp only [Finset.sum_const, nsmul_eq_mul] at hsumlo
  have hroot : 0 < Real.sqrt μ := Real.sqrt_pos_of_pos hμ
  have hle : (s.card : ℝ) * (1 / (2 * Real.sqrt μ)) ≤ Real.sqrt X := hsumlo.trans hsum
  calc
    (s.card : ℝ) = ((s.card : ℝ) * (1 / (2 * Real.sqrt μ))) * (2 * Real.sqrt μ) := by field_simp
    _ ≤ Real.sqrt X * (2 * Real.sqrt μ) := mul_le_mul_of_nonneg_right hle (by positivity)
    _ = 2 * v := by rw [show Real.sqrt X * (2 * Real.sqrt μ) = 2 * (Real.sqrt μ * Real.sqrt X) by ring,
      ← Real.sqrt_mul hμ.le, hid, Real.sqrt_sq hv]

set_option maxHeartbeats 800000 in
lemma outer_count (A r : ℕ → ℝ) (N L : ℕ) {μ γ R X v : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hv : 0 ≤ v)
    (hA : Monotone A) (hA0 : 0 ≤ A 0) (hAN : A N < X)
    (hr : ∀ k < N, 0 < r k)
    (hrec : ∀ k < N, A (k + 1) = A k + min 1 (μ / (γ * r k)) * trialWeight μ (A k))
    (hdiss : (∑ k ∈ Finset.range N, (A k + trialWeight μ (A k)) * min μ (γ * r k) * r k ^ 2) ≤ 2 * R ^ 2)
    (hscale : μ ^ 2 * v ^ 3 = γ ^ 2 * R ^ 2) (hXscale : μ * X = v ^ 2)
    (hcover : μ * X ≤ (2 : ℝ) ^ (L + 1)) :
    (N : ℝ) ≤ (2 + 4 * ((L : ℝ) + 2)) * v := by
  classical
  let S := (Finset.range N).filter (fun k => γ * r k ≤ μ)
  let low := (Finset.range N).filter (fun k => μ < γ * r k ∧ A k < μ⁻¹)
  let high := fun j => (Finset.range N).filter
    (fun k => μ < γ * r k ∧ (2 : ℝ) ^ j / μ ≤ A k ∧ A k < (2 : ℝ) ^ (j + 1) / μ)
  let weight := fun k => (A k + trialWeight μ (A k)) * min μ (γ * r k)
  have hpos (k : ℕ) : 0 ≤ A k := hA0.trans (hA (Nat.zero_le k))
  have hw : ∀ k ∈ Finset.range N, 0 ≤ weight k := by
    intro k hk
    exact mul_nonneg (add_nonneg (hpos k) (trialWeight_pos hμ (hpos k)).le)
      (le_min hμ.le (mul_pos hγ (hr k (Finset.mem_range.mp hk))).le)
  have hScard : (S.card : ℝ) ≤ 2 * v := by
    apply success_card S A N hμ hv hA hA0 (Finset.filter_subset _ _) hAN.le ?_ hXscale
    intro k hk
    obtain ⟨hk, hs⟩ := Finset.mem_filter.mp hk
    rw [hrec k (Finset.mem_range.mp hk), min_eq_left ((one_le_div (mul_pos hγ (hr k (Finset.mem_range.mp hk)))).mpr hs), one_mul]
  have hlowV : (∑ k ∈ low, r k ^ 2) ≤ 2 * R ^ 2 := by
    have h := selected_radii_bound low (Finset.range N) weight r (Finset.filter_subset _ _)
      (by norm_num : (0 : ℝ) < 1) hw (fun k hk => ?_) hdiss
    · simpa using h
    · obtain ⟨_, hf, _⟩ := Finset.mem_filter.mp hk
      have ht := trialWeight_lower hμ (hpos k)
      have hm := mul_le_mul_of_nonneg_left ht hμ.le
      rw [mul_inv_cancel₀ hμ.ne'] at hm
      dsimp only [weight]
      rw [min_eq_left hf.le]
      nlinarith only [hm, mul_nonneg hμ.le (hpos k)]
  have hlowcard : (low.card : ℝ) ≤ 4 * v := by
    apply low_failure_card low A r hμ hγ hv hA hA0
      (fun k hk => hr k (Finset.mem_range.mp (Finset.mem_filter.mp hk).1))
      (fun k hk => (Finset.mem_filter.mp hk).2.1)
      (fun k hk => (Finset.mem_filter.mp hk).2.2.le)
      (fun k hk => hrec k (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)) hlowV hscale
  have hhighcard (j : ℕ) : ((high j).card : ℝ) ≤ 4 * v := by
    let b := (2 : ℝ) ^ j / μ
    have hb : 0 < b := by dsimp only [b]; positivity
    have hμb : 1 ≤ μ * b := by
      dsimp only [b]
      rw [mul_div_cancel₀ _ hμ.ne']
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hV : (∑ k ∈ high j, r k ^ 2) ≤ 2 * R ^ 2 / (μ * b) := by
      apply selected_radii_bound (high j) (Finset.range N) weight r (Finset.filter_subset _ _)
        (mul_pos hμ hb) hw ?_ hdiss
      intro k hk
      obtain ⟨_, hf, hlo, _⟩ := Finset.mem_filter.mp hk
      dsimp only [weight]
      rw [min_eq_left hf.le]
      have hm := mul_le_mul_of_nonneg_left hlo hμ.le
      have ha := mul_nonneg hμ.le (trialWeight_pos hμ (hpos k)).le
      change μ * b ≤ (A k + trialWeight μ (A k)) * μ
      nlinarith only [hm, ha]
    apply high_failure_card (high j) A r hμ hγ hv hb hμb hA hA0
      (fun k hk => hr k (Finset.mem_range.mp (Finset.mem_filter.mp hk).1))
      (fun k hk => (Finset.mem_filter.mp hk).2.1)
      (fun k hk => (Finset.mem_filter.mp hk).2.2.1) ?_
      (fun k hk => hrec k (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)) hV hscale
    intro k hk
    have h := (Finset.mem_filter.mp hk).2.2.2.le
    convert h using 1
    dsimp only [b]
    rw [pow_succ]
    ring
  have hsub : Finset.range N ⊆ (S ∪ low) ∪ (Finset.range (L + 1)).biUnion high := by
    intro k hk
    by_cases hs : γ * r k ≤ μ
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk, hs⟩))
    have hf : μ < γ * r k := lt_of_not_ge hs
    by_cases hl : A k < μ⁻¹
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, hf, hl⟩))
    have ht : 1 ≤ μ * A k := by
      have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hl) hμ.le
      rwa [mul_inv_cancel₀ hμ.ne'] at hm
    have htupper : μ * A k < (2 : ℝ) ^ (L + 1) :=
      (mul_lt_mul_of_pos_left ((hA (Nat.le_of_lt (Finset.mem_range.mp hk))).trans_lt hAN) hμ).trans_le hcover
    obtain ⟨j, hj, hjlo, hjhi⟩ := dyadic_cover ht L htupper
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hj), Finset.mem_filter.mpr ⟨hk, hf, ?_, ?_⟩⟩
    · apply (div_le_iff₀ hμ).mpr
      nlinarith only [hjlo]
    · apply (lt_div_iff₀ hμ).mpr
      nlinarith only [hjhi]
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le (S ∪ low) ((Finset.range (L + 1)).biUnion high)
  have hu' := Finset.card_union_le S low
  have hb := Finset.card_biUnion_le (s := Finset.range (L + 1)) (t := high)
  have hn : N ≤ S.card + low.card + ∑ j ∈ Finset.range (L + 1), (high j).card := by
    rw [Finset.card_range] at hc
    omega
  have hn' : (N : ℝ) ≤ (S.card : ℝ) + (low.card : ℝ) + ∑ j ∈ Finset.range (L + 1), ((high j).card : ℝ) := by
    exact_mod_cast hn
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range (L + 1)) => hhighcard j)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hsum
  nlinarith only [hn', hScard, hlowcard, hsum]

lemma advance_weight_mono (state : State E) (z s : E) {μ γ : ℝ}
    (hμ : 0 < μ) (hγ : 0 ≤ γ) (hA : 0 ≤ state.weight) :
    state.weight ≤ (advance E μ γ state z s).weight := by
  have ha := trialWeight_pos hμ hA
  have hb : 0 ≤ min 1 (μ / (γ * ‖z - center E μ state‖)) :=
    le_min (by norm_num) (div_nonneg hμ.le (mul_nonneg hγ (norm_nonneg _)))
  change state.weight ≤ state.weight + min 1 (μ / (γ * ‖z - center E μ state‖)) * trialWeight μ state.weight
  exact le_add_of_nonneg_right (mul_nonneg hb ha.le)

end LongTails.Proofs.CompositeCubicAcceleration
