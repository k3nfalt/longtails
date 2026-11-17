import LongTails.Proofs.DashaTracking

namespace LongTails.Proofs.DashaScalingRange

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma local_update_bound (g h hnext compressed : E) (a η H q δ M G D : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hH : 0 ≤ H)
    (hq : 0 ≤ q) (hM : 0 ≤ M) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hg : ‖g‖ ≤ M) (hh : ‖h‖ ≤ G + H * D)
    (hd : ‖hnext - h‖ ≤ H * η * M)
    (hc : ‖compressed‖ ≤ 2 * q * ‖hnext - h - a • (g - h)‖ + δ) :
    ‖g + compressed‖ ≤ M + 2 * q * ((1 + H * η) * M + G + H * D) + δ := by
  have he : ‖g - h‖ ≤ M + G + H * D :=
    (norm_sub_le g h).trans (by linarith)
  have haabs : ‖a‖ = a := Real.norm_of_nonneg ha
  have hv : ‖hnext - h - a • (g - h)‖ ≤ (1 + H * η) * M + G + H * D := by
    calc
      _ ≤ ‖hnext - h‖ + ‖a • (g - h)‖ := norm_sub_le _ _
      _ = ‖hnext - h‖ + a * ‖g - h‖ := by rw [norm_smul, haabs]
      _ ≤ H * η * M + a * (M + G + H * D) :=
        add_le_add hd (mul_le_mul_of_nonneg_left he ha)
      _ ≤ (1 + H * η) * M + G + H * D := by
        have hp := mul_le_mul_of_nonneg_right ha1 (show 0 ≤ M + G + H * D by positivity)
        nlinarith
  have hp := mul_le_mul_of_nonneg_left hv (show 0 ≤ 2 * q by positivity)
  have hn := norm_add_le g compressed
  linarith

lemma state_bound_step (M D Mnext Dnext G H η q δ : ℝ)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hη : 0 ≤ η) (hq : 0 ≤ q) (hδ : 0 ≤ δ)
    (hm : Mnext ≤ M + 2 * q * ((1 + H * η) * M + G + H * D) + δ)
    (hd : Dnext ≤ D + η * M) :
    Mnext + G + H * Dnext + δ ≤
      (2 + 2 * q) * (1 + H * η) * (M + G + H * D + δ) := by
  have hd' := mul_le_mul_of_nonneg_left hd hH
  have he : 0 ≤ (1 + (2 + 2 * q) * (H * η)) * (G + H * D) +
      (2 * q + (2 + 2 * q) * (H * η)) * δ + (1 + H * η) * M := by positivity
  nlinarith only [hm, hd', he]

omit [NormedSpace ℝ E] in
lemma local_norm_of_mean_square {n : ℕ+} (v : Fin n → E) (H D : ℝ)
    (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hv : (1 / (n : ℝ)) * (∑ i, ‖v i‖ ^ 2) ≤ H ^ 2 * D ^ 2) (i : Fin n) :
    ‖v i‖ ≤ Real.sqrt (n : ℝ) * H * D := by
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hsum : ‖v i‖ ^ 2 ≤ ∑ j, ‖v j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖v j‖) (Finset.mem_univ i)
  have hbound : (∑ j, ‖v j‖ ^ 2) ≤ (n : ℝ) * (H ^ 2 * D ^ 2) := by
    calc
      _ = (n : ℝ) * ((1 / (n : ℝ)) * (∑ j, ‖v j‖ ^ 2)) := by field_simp [hn.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hv hn.le
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ (n : ℝ) * (H ^ 2 * D ^ 2) := hsum.trans hbound
    _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hn.le]; ring

lemma innovation_norm_bound (g h hnext : E) (a η H δ M G D : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hη : 0 ≤ η) (hH : 0 ≤ H) (hδ : 0 ≤ δ)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hg : ‖g‖ ≤ M) (hh : ‖h‖ ≤ G + H * D) (hd : ‖hnext - h‖ ≤ H * η * M) :
    ‖hnext - h - a • (g - h)‖ ≤ (1 + H * η) * (M + G + H * D + δ) := by
  have he : ‖g - h‖ ≤ M + G + H * D := (norm_sub_le g h).trans (by linarith)
  have ht := norm_sub_le (hnext - h) (a • (g - h))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha] at ht
  have hscaled := mul_le_mul_of_nonneg_left he ha
  have hsmall := mul_le_mul_of_nonneg_right ha1 (show 0 ≤ M + G + H * D by positivity)
  have hrem : 0 ≤ H * η * (G + H * D) + (1 + H * η) * δ := by positivity
  nlinarith only [ht, hd, hscaled, hsmall, hrem]

end LongTails.Proofs.DashaScalingRange
