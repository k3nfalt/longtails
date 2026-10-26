import LongTails.Proofs.AdamSymmetricGeometry

namespace LongTails.Proofs.AdamNoiseCoupling

open LongTails.Proofs.AdamSymmetricGeometry

lemma sum_abs_affine_of_symmetric {Ω : Type*} [Fintype Ω] (e : Ω ≃ Ω)
    (N : Ω → ℝ) (hN : ∀ ω, N (e ω) = -N ω) (m α : ℝ) (hα : 0 ≤ α) :
    α * ∑ ω, |N ω| ≤ ∑ ω, |m + α * N ω| := by
  have heq : ∑ ω, |m - α * N ω| = ∑ ω, |m + α * N ω| := by
    calc
      ∑ ω, |m - α * N ω| = ∑ ω, |m + α * N (e ω)| := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [hN]
        congr 1
        ring
      _ = ∑ ω, |m + α * N ω| := e.sum_comp (fun ω => |m + α * N ω|)
  have hp : 2 * α * ∑ ω, |N ω| ≤
      (∑ ω, |m + α * N ω|) + ∑ ω, |m - α * N ω| := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ω _
    simpa only [abs_mul, abs_of_nonneg hα, mul_assoc] using
      symmetric_pair_absolute_lower m (α * N ω)
  rw [heq] at hp
  linarith

lemma finite_direction_coupling {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (e : Ω ≃ Ω) (N U δ : Ω → ℝ) (m α H h t B s : ℝ)
    (hN : ∀ ω, N (e ω) = -N ω) (hα : 0 ≤ α) (hαt : 1 ≤ α * t)
    (hH : 0 < H) (ht : 1 ≤ t) (hB : 0 < B) (hs : 0 < s) (hh : 0 ≤ h)
    (hnoise : (Fintype.card Ω : ℝ) * s ≤ B * ∑ ω, |N ω|)
    (hU : ∀ ω, |m + α * N ω| ≤ H * |U ω|)
    (hδ : ∀ ω, H * |δ ω| ≤ 8 * h * t) :
    ∑ ω, |δ ω| ≤ (8 * h * B * t ^ 2 / s) * ∑ ω, |U ω| := by
  have hcard : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hsumU : α * ∑ ω, |N ω| ≤ H * ∑ ω, |U ω| := by
    refine (sum_abs_affine_of_symmetric e N hN m α hα).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun ω _ => hU ω
  have hsumδ : H * ∑ ω, |δ ω| ≤ (Fintype.card Ω : ℝ) * (8 * h * t) := by
    rw [Finset.mul_sum]
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hδ ω)
  have hlow : (Fintype.card Ω : ℝ) * s ≤ B * t * H * ∑ ω, |U ω| := by
    have h₁ := mul_le_mul_of_nonneg_left hsumU (show 0 ≤ B * t by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hnoise (show 0 ≤ α * t by positivity)
    have h₃ := mul_le_mul_of_nonneg_right hαt (show 0 ≤ (Fintype.card Ω : ℝ) * s by positivity)
    nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hs]
  have h₄ := mul_le_mul_of_nonneg_right hsumδ hs.le
  have h₅ := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 8 * h * t by positivity)
  nlinarith

lemma sign_sum_absolute_lower (n : ℕ) :
    (Fintype.card (Fin (n + 1) → Bool) : ℝ) ≤
      ∑ ω : Fin (n + 1) → Bool, |∑ j, if ω j then (1 : ℝ) else -1| := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp
    (fun ω => |∑ j, if ω j then (1 : ℝ) else -1|)]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.sum_univ_succ, Fin.cons_zero,
    Fin.cons_succ, Bool.false_eq_true, ↓reduceIte]
  rw [← Finset.sum_add_distrib]
  have hp : ∀ ω : Fin n → Bool, (2 : ℝ) ≤
      |1 + ∑ j, if ω j then (1 : ℝ) else -1| +
        |-1 + ∑ j, if ω j then (1 : ℝ) else -1| := by
    intro ω
    have h := symmetric_pair_absolute_lower (∑ j, if ω j then (1 : ℝ) else -1) 1
    norm_num at h
    simpa only [sub_eq_add_neg, add_comm] using h
  have h := Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hp ω)
  simpa [Fintype.card_fun, Fintype.card_bool, pow_succ] using h

lemma rms_denominator_bounds {V w μ N τ s : ℝ} (hV : 0 ≤ V) (hw : 0 ≤ w)
    (hτ : 0 ≤ τ) (hN : |N| ≤ s) :
    Real.sqrt V + τ ≤ Real.sqrt (V + w * (μ + N) ^ 2) + τ ∧
    Real.sqrt w * |μ + N| ≤ Real.sqrt (V + w * (μ + N) ^ 2) + τ ∧
    Real.sqrt (V + w * (μ + N) ^ 2) + τ ≤
      Real.sqrt V + τ + Real.sqrt w * (|μ| + s) := by
  have hsqrt : Real.sqrt (w * (μ + N) ^ 2) = Real.sqrt w * |μ + N| := by
    rw [Real.sqrt_mul hw, Real.sqrt_sq_eq_abs]
  refine ⟨?_, ?_, ?_⟩
  · exact add_le_add (Real.sqrt_le_sqrt (show V ≤ V + w * (μ + N) ^ 2 by nlinarith [mul_nonneg hw (sq_nonneg (μ + N))])) (le_refl τ)
  · have h := Real.sqrt_le_sqrt (show w * (μ + N) ^ 2 ≤ V + w * (μ + N) ^ 2 by linarith)
    rw [hsqrt] at h
    linarith
  · have hroot : Real.sqrt (V + w * (μ + N) ^ 2) ≤
        Real.sqrt V + Real.sqrt (w * (μ + N) ^ 2) := by
      rw [Real.sqrt_le_left (by positivity)]
      have hsq₁ := Real.sq_sqrt hV
      have hsq₂ := Real.sq_sqrt (mul_nonneg hw (sq_nonneg (μ + N)))
      nlinarith [mul_nonneg (Real.sqrt_nonneg V) (Real.sqrt_nonneg (w * (μ + N) ^ 2))]
    rw [hsqrt] at hroot
    have habs : |μ + N| ≤ |μ| + s := (abs_add_le μ N).trans (add_le_add (le_refl _) hN)
    have hmul := mul_le_mul_of_nonneg_left habs (Real.sqrt_nonneg w)
    linarith

lemma bounded_history_coupling {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (e : Ω ≃ Ω) (N δ : Ω → ℝ) (M μ V α w τ h t B s : ℝ)
    (hNsym : ∀ ω, N (e ω) = -N ω) (hNbound : ∀ ω, |N ω| ≤ s)
    (hnoise : (Fintype.card Ω : ℝ) * s ≤ B * ∑ ω, |N ω|)
    (hV : 0 ≤ V) (hw : 0 < w) (hw₁ : w ≤ 1) (hτ : 0 ≤ τ)
    (hα : 0 ≤ α) (hαt : 1 ≤ α * t) (ht : 1 ≤ t) (hB : 0 < B) (hs : 0 < s)
    (hhs : s ≤ h)
    (hδ : ∀ ω, |δ ω| ≤ 2 * t)
    (hDδ : ∀ ω, (Real.sqrt (V + w * (μ + N ω) ^ 2) + τ) * |δ ω| ≤ h * (1 + t))
    (hM : ∀ ω, |M + α * (μ + N ω)| ≤ t * Real.sqrt (V + w * (μ + N ω) ^ 2)) :
    ∑ ω, |δ ω| ≤ (8 * h * B * t ^ 2 / s) *
      ∑ ω, |(M + α * (μ + N ω)) / (Real.sqrt (V + w * (μ + N ω) ^ 2) + τ)| := by
  let H := Real.sqrt V + τ + Real.sqrt w * (|μ| + s)
  have hH : 0 < H := by dsimp [H]; positivity
  have hh : 0 ≤ h := hs.le.trans hhs
  apply finite_direction_coupling e N _ δ (M + α * μ) α H h t B s hNsym hα hαt hH ht hB hs hh hnoise
  · intro ω
    have hb := rms_denominator_bounds (μ := μ) hV hw.le hτ (hNbound ω)
    have hp := normalized_direction_product (Real.sqrt_nonneg _) hτ (hM ω)
    have hpabs := congrArg abs hp
    rw [abs_mul, abs_of_nonneg (show 0 ≤ Real.sqrt (V + w * (μ + N ω) ^ 2) + τ by positivity)] at hpabs
    have hm := mul_le_mul_of_nonneg_right hb.2.2
      (abs_nonneg ((M + α * (μ + N ω)) / (Real.sqrt (V + w * (μ + N ω) ^ 2) + τ)))
    rw [hpabs] at hm
    convert hm using 1
    congr 1
    ring
  · intro ω
    have hb := rms_denominator_bounds (μ := μ) hV hw.le hτ (hNbound ω)
    have hen := bounded_noise_denominator_envelope (Real.sqrt_nonneg w)
      (Real.sqrt_le_one.mpr hw₁) (hNbound ω) hhs hb.1 hb.2.1
    exact bounded_noise_direction_envelope ht hh hen (hδ ω) (hDδ ω)

end LongTails.Proofs.AdamNoiseCoupling
