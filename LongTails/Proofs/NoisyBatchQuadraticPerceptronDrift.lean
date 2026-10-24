import LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry
import LongTails.Proofs.NoisyBatchQuadraticPerceptronGaussian

namespace LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift

open LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry
open LongTails.Setups.NoisyBatchQuadraticPerceptron
open Classical
open scoped RealInnerProductSpace
lemma averaged_direction (P : Public) (data : Data P) (w : Weights P.dimension) :
    (P.count : ℝ)⁻¹ • (∑ i : Fin P.count,
      if (answer (data i) w).margin ≤ 0 then (answer (data i) w).direction else 0) =
    WithLp.toLp 2 (w.ofLp.2 • selected data w.ofLp.1 w.ofLp.2,
      ⟪selected data w.ofLp.1 w.ofLp.2, w.ofLp.1⟫) := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · simp only [WithLp.ofLp_smul, WithLp.ofLp_sum, Prod.smul_fst, Prod.fst_sum]
    unfold selected answer
    simp only [smul_comm w.ofLp.2, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  · simp only [WithLp.ofLp_smul, WithLp.ofLp_sum, Prod.smul_snd, Prod.snd_sum]
    unfold selected answer
    rw [real_inner_smul_left, sum_inner]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
lemma selected_reflect (P : Public) (data : Data P) (c : Features P.dimension) (v : ℝ) :
    selected data (-c) (-v) = selected data c v := by
  simp [selected]

lemma potential_reflect (P : Public) (data : Data P) (η : ℝ)
    (c : Features P.dimension) (v : ℝ) : potential data η (-c) (-v) = potential data η c v := by
  unfold potential
  rw [positive_neg, negative_neg]
  simp only [norm_neg, neg_sq, inner_neg_right, neg_neg]
  ring

lemma positive_step_lower (P : Public) (data : Data P)
    (c : Features P.dimension) (v η : ℝ) (hv : 0 ≤ v) (hη : 0 ≤ η)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    positive data c - η * v * P.radius ^ 2 ≤
      positive data (c + (η * v) • selected data c v) := by
  have hr : 0 ≤ P.radius := (norm_nonneg (data 0)).trans (hR 0)
  have h := (abs_le.mp (abs_positive_shift_le P data c ((η * v) • selected data c v) hR)).1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hη hv)] at h
  have hb := mul_le_mul_of_nonneg_left (norm_selected_le P data c v hR)
    (mul_nonneg hr (mul_nonneg hη hv))
  nlinarith
noncomputable def corePotential {P : Public} (data : Data P) (η : ℝ)
    (c : Features P.dimension) (v : ℝ) : ℝ := ‖c‖ ^ 2 - v ^ 2 + η * v * ⟪mean data, c⟫

lemma core_step_identity_pos (P : Public) (data : Data P) (η : ℝ)
    (c : Features P.dimension) (v : ℝ) (hv : 0 < v) :
    corePotential data η (c + (η * v) • selected data c v) (v - η * negative data c) -
      corePotential data η c v =
      η ^ 2 * (-positive data c * negative data c +
        v * (v - η * negative data c) * ⟪mean data, selected data c v⟫ +
        v ^ 2 * ‖selected data c v‖ ^ 2) := by
  have h := QuadraticPerceptronBatchPotential.batch_potential_identity c (selected data c v)
    (mean data) v η
  rw [selected_inner_pos P data c v hv, ← positive_negative_difference P data c] at h
  unfold corePotential
  rw [← positive_negative_difference P data c]
  convert h using 1 <;> ring

lemma core_step_nonflip (P : Public) (data : Data P) (η : ℝ)
    (c : Features P.dimension) (v : ℝ) (hv : 0 < v)
    (hflip : η * negative data c ≤ v) (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    corePotential data η (c + (η * v) • selected data c v) (v - η * negative data c) -
      corePotential data η c v ≤
      η ^ 2 * (P.radius ^ 2 * v * (2 * v - η * negative data c) -
        positive data c * negative data c) := by
  rw [core_step_identity_pos P data η c v hv]
  have hr : 0 ≤ P.radius := (norm_nonneg (data 0)).trans (hR 0)
  have hg := norm_selected_le P data c v hR
  have hm := norm_mean_le P data hR
  have hi : ⟪mean data, selected data c v⟫ ≤ P.radius ^ 2 := by
    have h := real_inner_le_norm (mean data) (selected data c v)
    have hb := mul_le_mul hm hg (norm_nonneg _) hr
    nlinarith
  have hg₂ : ‖selected data c v‖ ^ 2 ≤ P.radius ^ 2 := by nlinarith [norm_nonneg (selected data c v)]
  have h₁ := mul_le_mul_of_nonneg_left hi (mul_nonneg hv.le (sub_nonneg.mpr hflip))
  have h₂ := mul_le_mul_of_nonneg_left hg₂ (sq_nonneg v)
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg η)
  nlinarith
lemma core_step_flip (P : Public) (data : Data P) (η : ℝ)
    (c : Features P.dimension) (v : ℝ) (hv : 0 < v)
    (hflip : v ≤ η * negative data c) (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    corePotential data η (c + (η * v) • selected data c v) (v - η * negative data c) -
      corePotential data η c v ≤
      η ^ 2 * negative data c * (η * v * P.radius ^ 2 - positive data c) := by
  rw [core_step_identity_pos P data η c v hv]
  have hr : 0 ≤ P.radius := (norm_nonneg (data 0)).trans (hR 0)
  have hg := norm_selected_le P data c v hR
  have hm := norm_mean_le P data hR
  have hi : -P.radius ^ 2 ≤ ⟪mean data, selected data c v⟫ := by
    have h := (abs_le.mp (abs_real_inner_le_norm (mean data) (selected data c v))).1
    have hb := mul_le_mul hm hg (norm_nonneg _) hr
    nlinarith
  have hg₂ : ‖selected data c v‖ ^ 2 ≤ P.radius ^ 2 := by nlinarith [norm_nonneg (selected data c v)]
  have h₁ := mul_le_mul_of_nonpos_left hi (mul_nonpos_of_nonneg_of_nonpos hv.le (sub_nonpos.mpr hflip))
  have h₂ := mul_le_mul_of_nonneg_left hg₂ (sq_nonneg v)
  have h₃ : -positive data c * negative data c +
      v * (v - η * negative data c) * ⟪mean data, selected data c v⟫ +
      v ^ 2 * ‖selected data c v‖ ^ 2 ≤
      negative data c * (η * v * P.radius ^ 2 - positive data c) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h₃ (sq_nonneg η)]
lemma potential_nonneg_output (P : Public) (data : Data P) (η : ℝ)
    (c : Features P.dimension) (v : ℝ) (hv : 0 ≤ v) (hη : 0 ≤ η) :
    potential data η c v = corePotential data η c v +
      2 * (max (v - η * positive data c) 0) ^ 2 := by
  have hq := mul_nonneg hη (negative_nonneg P data c)
  unfold potential corePotential
  rw [max_eq_right (show -v - η * negative data c ≤ 0 by linarith)]
  ring

lemma potential_step_nonflip (P : Public) (data : Data P) (η : ℝ)
    (c : Features P.dimension) (v : ℝ) (hv : 0 < v) (hη : 0 < η)
    (hescape : 4 * η * P.radius ^ 2 * v ≤ negative data c)
    (hflip : η * negative data c ≤ v) (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    potential data η (c + (η * v) • selected data c v) (v - η * negative data c) -
      potential data η c v ≤
      -(η ^ 2 * (positive data c * negative data c + P.radius ^ 2 * v ^ 2)) / 4 := by
  rw [potential_nonneg_output P data η _ _ (sub_nonneg.mpr hflip) hη.le,
    potential_nonneg_output P data η c v hv.le hη.le]
  have hc := core_step_nonflip P data η c v hv hflip hR
  have hs := QuadraticPerceptronBatchPotential.nonflip_drift_scaled
    (positive data c) (negative data c) v η P.radius hv hη hescape hflip
  have hl := mul_le_mul_of_nonneg_left (positive_step_lower P data c v η hv.le hη.le hR) hη.le
  have hm : max (v - η * negative data c - η * positive data (c + (η * v) • selected data c v)) 0 ≤
      max (v - η * positive data c - η * negative data c + η ^ 2 * v * P.radius ^ 2) 0 :=
    max_le_max (by nlinarith) le_rfl
  have h₁ := le_max_right (v - η * negative data c - η * positive data (c + (η * v) • selected data c v)) 0
  have h₂ := le_max_right (v - η * positive data c - η * negative data c + η ^ 2 * v * P.radius ^ 2) 0
  nlinarith [hc, hs]
lemma potential_step_flip (P : Public) (data : Data P) (η : ℝ)
    (c : Features P.dimension) (v : ℝ) (hv : 0 < v) (hη : 0 < η)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256)
    (hflip : v ≤ η * negative data c)
    (hnext : 4 * η * P.radius ^ 2 * (η * negative data c - v) ≤
      positive data (c + (η * v) • selected data c v))
    (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    potential data η (c + (η * v) • selected data c v) (v - η * negative data c) -
      potential data η c v ≤
      -(η ^ 2 * (positive data c * negative data c + P.radius ^ 2 * v ^ 2)) / 4 := by
  have hg := norm_selected_le P data c v hR
  have hr : 0 ≤ P.radius := (norm_nonneg (data 0)).trans (hR 0)
  have hg₂ : ‖selected data c v‖ ^ 2 ≤ P.radius ^ 2 := by
    nlinarith [norm_nonneg (selected data c v)]
  have hkg := mul_le_mul_of_nonneg_left hg₂ (sq_nonneg η)
  have hpos : 0 ≤ 1 - η ^ 2 * ‖selected data c v‖ ^ 2 := by nlinarith
  have hi := inherited_gap P data c v η hv hη.le
  have hb : 0 ≤ η * negative data (c + (η * v) • selected data c v) +
      (v - η * negative data c) := (mul_nonneg hv.le hpos).trans hi
  have hp := mul_nonneg hη.le (positive_nonneg P data (c + (η * v) • selected data c v))
  have he : potential data η (c + (η * v) • selected data c v) (v - η * negative data c) =
      corePotential data η (c + (η * v) • selected data c v) (v - η * negative data c) := by
    unfold potential corePotential
    rw [max_eq_right (show v - η * negative data c - η * positive data (c + (η * v) • selected data c v) ≤ 0 by linarith),
      max_eq_right (show -(v - η * negative data c) - η * negative data (c + (η * v) • selected data c v) ≤ 0 by linarith)]
    ring
  rw [he, potential_nonneg_output P data η c v hv.le hη.le]
  have hc := core_step_flip P data η c v hv hflip hR
  have hn := hnext.trans (positive_step_upper P data c v η hv.le hη.le hR)
  have hs := QuadraticPerceptronBatchPotential.flip_drift_scaled (positive data c)
    (negative data c) v η P.radius (positive_nonneg P data c) hv hη hk hflip hn
  linarith
def Escape {P : Public} (data : Data P) (η : ℝ) (c : Features P.dimension) (v : ℝ) : Prop :=
  (0 < v ∧ negative data c ≤ 4 * η * P.radius ^ 2 * v) ∨
    (v < 0 ∧ positive data c ≤ 4 * η * P.radius ^ 2 * (-v))

lemma escape_reflect (P : Public) (data : Data P) (η : ℝ)
    (c : Features P.dimension) (v : ℝ) : Escape data η (-c) (-v) ↔ Escape data η c v := by
  unfold Escape
  rw [positive_neg, negative_neg]
  constructor
  · rintro (⟨hv, h⟩ | ⟨hv, h⟩)
    · exact Or.inr ⟨by linarith, h⟩
    · exact Or.inl ⟨by linarith, by simpa using h⟩
  · rintro (⟨hv, h⟩ | ⟨hv, h⟩)
    · exact Or.inr ⟨by linarith, by simpa using h⟩
    · exact Or.inl ⟨by linarith, h⟩

lemma potential_step_pos (P : Public) (data : Data P) (η : ℝ)
    (c : Features P.dimension) (v : ℝ) (hv : 0 < v) (hη : 0 < η)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256)
    (hcurrent : ¬Escape data η c v)
    (hnext : ¬Escape data η (c + (η * v) • selected data c v)
      (v + η * ⟪selected data c v, c⟫))
    (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    potential data η (c + (η * v) • selected data c v)
      (v + η * ⟪selected data c v, c⟫) - potential data η c v ≤
      -(η ^ 2 * (positive data c * negative data c + P.radius ^ 2 * v ^ 2)) / 4 := by
  rw [selected_inner_pos P data c v hv] at hnext ⊢
  simp only [mul_neg, ← sub_eq_add_neg] at hnext ⊢
  by_cases hf : η * negative data c ≤ v
  · have he : 4 * η * P.radius ^ 2 * v ≤ negative data c := by
      by_contra hh
      exact hcurrent (Or.inl ⟨hv, le_of_not_ge hh⟩)
    exact potential_step_nonflip P data η c v hv hη he hf hR
  · have he : 4 * η * P.radius ^ 2 * (η * negative data c - v) ≤
        positive data (c + (η * v) • selected data c v) := by
      by_contra hh
      apply hnext
      right
      constructor
      · linarith
      · have h := le_of_not_ge hh
        convert h using 1
        ring
    exact potential_step_flip P data η c v hv hη hk (le_of_not_ge hf) he hR
lemma potential_step_drift (P : Public) (data : Data P) (η : ℝ)
    (c : Features P.dimension) (v : ℝ) (hv : v ≠ 0) (hη : 0 < η)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256)
    (hcurrent : ¬Escape data η c v)
    (hnext : ¬Escape data η (c + (η * v) • selected data c v)
      (v + η * ⟪selected data c v, c⟫))
    (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    potential data η (c + (η * v) • selected data c v)
      (v + η * ⟪selected data c v, c⟫) - potential data η c v ≤
      -(η ^ 2 * (positive data c * negative data c + P.radius ^ 2 * v ^ 2)) / 4 := by
  by_cases hvp : 0 < v
  · exact potential_step_pos P data η c v hvp hη hk hcurrent hnext hR
  · have hvn : 0 < -v := by rcases lt_or_gt_of_ne hv with h | h <;> linarith
    have hc : -c + (η * -v) • selected data (-c) (-v) =
        -(c + (η * v) • selected data c v) := by
      rw [selected_reflect]
      module
    have hv' : -v + η * ⟪selected data (-c) (-v), -c⟫ =
        -(v + η * ⟪selected data c v, c⟫) := by
      rw [selected_reflect, inner_neg_right]
      ring
    have hcur := (escape_reflect P data η c v).not.mpr hcurrent
    have hn : ¬Escape data η (-c + (η * -v) • selected data (-c) (-v))
        (-v + η * ⟪selected data (-c) (-v), -c⟫) := by
      rw [hc, hv', escape_reflect]
      exact hnext
    have h := potential_step_pos P data η (-c) (-v) hvn hη hk hcur hn hR
    rw [hc, hv', potential_reflect, potential_reflect, positive_neg, negative_neg, neg_sq] at h
    simpa only [mul_comm (negative data c) (positive data c)] using h
open MeasureTheory ProbabilityTheory NoisyBatchQuadraticPerceptronGaussian
lemma gaussian_step_drift (P : Public) (data : Data P) (η σ : ℝ)
    (c : Features P.dimension) (v : ℝ) (hv : v ≠ 0) (hη : 0 < η)
    (hsmall : η * P.radius ≤ 1 / 16) (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256)
    (hcurrent : ¬Escape data η c v)
    (hnext : ¬Escape data η (c + (η * v) • selected data c v)
      (v + η * ⟪selected data c v, c⟫))
    (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    let w : Weights P.dimension := WithLp.toLp 2
      (c + (η * v) • selected data c v, v + η * ⟪selected data c v, c⟫)
    (∫ z : Weights P.dimension, potential data η (w + σ • z).ofLp.1
      (w + σ • z).ofLp.2 ∂stdGaussian (Weights P.dimension)) ≤
      potential data η c v - η ^ 2 * (positive data c * negative data c + P.radius ^ 2 * v ^ 2) / 4 +
        6 * σ ^ 2 * (P.dimension + 1) := by
  dsimp only
  have hg := gaussian_potential_upper P data η σ
    (WithLp.toLp 2 (c + (η * v) • selected data c v, v + η * ⟪selected data c v, c⟫)) hη.le hsmall hR
  rw [weights_finrank] at hg
  simp only [Nat.cast_add, Nat.cast_one] at hg
  have hd := potential_step_drift P data η c v hv hη hk hcurrent hnext hR
  linarith

lemma step_size_bounds (P : Public) (hδ : 0 < P.margin) (hR : P.margin ≤ P.radius) :
    0 < P.margin / (8 * ((P.count : ℝ) + 1) * P.radius ^ 2) ∧
      P.margin / (8 * ((P.count : ℝ) + 1) * P.radius ^ 2) * P.radius ≤ 1 / 16 := by
  have hr : 0 < P.radius := lt_of_lt_of_le hδ hR
  have hn : (1 : ℝ) ≤ P.count := by exact_mod_cast P.count.pos
  constructor
  · positivity
  · have hd : 0 < 8 * ((P.count : ℝ) + 1) * P.radius ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    have h₁ := mul_le_mul_of_nonneg_right hR hr.le
    have h₂ := mul_le_mul_of_nonneg_right hn (sq_nonneg P.radius)
    nlinarith

lemma selected_wrong_inner (P : Public) (data : Data P) (c : Features P.dimension) (v : ℝ) :
    v * ⟪selected data c v, c⟫ ≤ 0 := by
  rcases lt_trichotomy 0 v with hv | hv | hv
  · rw [selected_inner_pos P data c v hv]
    nlinarith [mul_nonneg hv.le (negative_nonneg P data c)]
  · rw [← hv]
    simp
  · rw [selected_inner_neg P data c v hv]
    exact mul_nonpos_of_nonpos_of_nonneg hv.le (positive_nonneg P data c)

lemma deterministic_energy_le (P : Public) (data : Data P) (η : ℝ)
    (c : Features P.dimension) (v : ℝ) (hη : 0 ≤ η)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    ‖c + (η * v) • selected data c v‖ ^ 2 + (v + η * ⟪selected data c v, c⟫) ^ 2 ≤
      (1 + η ^ 2 * P.radius ^ 2) * (‖c‖ ^ 2 + v ^ 2) := by
  have hr : 0 ≤ P.radius := (norm_nonneg (data 0)).trans (hR 0)
  have hg := norm_selected_le P data c v hR
  have hg₂ : ‖selected data c v‖ ^ 2 ≤ P.radius ^ 2 := by
    nlinarith [norm_nonneg (selected data c v)]
  have hi := (abs_real_inner_le_norm (selected data c v) c).trans
    (mul_le_mul_of_nonneg_right hg (norm_nonneg c))
  have hi₂ : ⟪selected data c v, c⟫ ^ 2 ≤ P.radius ^ 2 * ‖c‖ ^ 2 := by
    nlinarith [sq_abs ⟪selected data c v, c⟫, abs_nonneg ⟪selected data c v, c⟫,
      mul_nonneg hr (norm_nonneg c)]
  have hc := mul_le_mul_of_nonneg_left (selected_wrong_inner P data c v) hη
  have h₁ := mul_le_mul_of_nonneg_left hg₂ (mul_nonneg (sq_nonneg η) (sq_nonneg v))
  have h₂ := mul_le_mul_of_nonneg_left hi₂ (sq_nonneg η)
  rw [norm_add_sq_real, real_inner_smul_right, real_inner_comm c (selected data c v),
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [real_inner_comm c (selected data c v)] at hc h₂
  nlinarith only [hc, h₁, h₂]

lemma deterministic_proposal (P : Public) (data : Data P) (η : ℝ) (w : Weights P.dimension) :
    w + (η / (P.count : ℝ)) • (∑ i : Fin P.count,
      if (answer (data i) w).margin ≤ 0 then (answer (data i) w).direction else 0) =
      WithLp.toLp 2 (w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2,
        w.ofLp.2 + η * inner ℝ (selected data w.ofLp.1 w.ofLp.2) w.ofLp.1) := by
  rw [div_eq_mul_inv, mul_smul, averaged_direction]
  apply WithLp.ofLp_injective
  simp [WithLp.ofLp_add, WithLp.ofLp_smul, smul_smul]
  rfl

end LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift
