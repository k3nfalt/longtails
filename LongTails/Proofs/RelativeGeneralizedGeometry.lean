import LongTails.Proofs.Clipping

open scoped RealInnerProductSpace

namespace OracleTemplate.RelativeGeneralized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma normal_inner_margin {c u x n : E} {R : ℝ} (hR : 0 < R)
    (hu : ‖u - c‖ ≤ R)
    (hn : ∀ w : E, ‖w - c‖ ≤ 2 * R → ⟪n, w - x⟫ ≤ 0) :
    R * ‖n‖ ≤ ⟪n, x - u⟫ := by
  by_cases hz : n = 0
  · simp [hz]
  have hnorm : 0 < ‖n‖ := norm_pos_iff.mpr hz
  have hw : ‖u + (R / ‖n‖) • n - c‖ ≤ 2 * R := by
    calc
      _ = ‖(u - c) + (R / ‖n‖) • n‖ := by congr 1; abel
      _ ≤ ‖u - c‖ + ‖(R / ‖n‖) • n‖ := norm_add_le _ _
      _ = ‖u - c‖ + R := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          div_mul_cancel₀ _ hnorm.ne']
      _ ≤ 2 * R := by linarith
  have hi := hn _ hw
  have he : u + (R / ‖n‖) • n - x = (R / ‖n‖) • n - (x - u) := by abel
  rw [he, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at hi
  have hm : R / ‖n‖ * ‖n‖ ^ 2 = R * ‖n‖ := by field_simp
  rw [hm] at hi
  linarith

lemma normal_norm_bound {c u x n h : E} {R : ℝ} (hR : 0 < R)
    (hu : ‖u - c‖ ≤ R) (hx : ‖x - c‖ ≤ 2 * R)
    (hn : ∀ w : E, ‖w - c‖ ≤ 2 * R → ⟪n, w - x⟫ ≤ 0)
    (hh : 0 ≤ ⟪h, x - u⟫) :
    ‖n‖ ≤ 3 * ‖h + n‖ := by
  have hm := normal_inner_margin hR hu hn
  have hd : ‖x - u‖ ≤ 3 * R := by
    calc
      _ ≤ ‖x - c‖ + ‖c - u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 3 * R := by rw [norm_sub_rev c u]; linarith
  have hi := real_inner_le_norm (h + n) (x - u)
  rw [inner_add_left] at hi
  have hb := mul_le_mul_of_nonneg_left hd (norm_nonneg (h + n))
  nlinarith

lemma relative_mapping_bound {c u x n h h' v e : E} {R α γ : ℝ}
    (hR : 0 < R) (hu : ‖u - c‖ ≤ R) (hx : ‖x - c‖ ≤ 2 * R)
    (hn : ∀ w : E, ‖w - c‖ ≤ 2 * R → ⟪n, w - x⟫ ≤ 0)
    (hh : 0 ≤ ⟪h', x - u⟫) (he : ‖e‖ ≤ α * ‖h‖)
    (hgrad : ‖h' - h‖ ≤ γ * ‖v‖) (hv : v = h + e + n) :
    (1 - 4 * α) * ‖h‖ ≤ (4 + 3 * γ) * ‖v‖ := by
  have hn' := normal_norm_bound hR hu hx hn hh
  have ht : ‖h' + n‖ ≤ (1 + γ) * ‖v‖ + α * ‖h‖ := by
    calc
      _ = ‖v + (h' - h) - e‖ := by congr 1; rw [hv]; abel
      _ ≤ ‖v + (h' - h)‖ + ‖e‖ := norm_sub_le _ _
      _ ≤ ‖v‖ + ‖h' - h‖ + ‖e‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (1 + γ) * ‖v‖ + α * ‖h‖ := by linarith
  have hb : ‖h‖ ≤ ‖v‖ + ‖e‖ + ‖n‖ := by
    calc
      _ = ‖v - e - n‖ := by congr 1; rw [hv]; abel
      _ ≤ ‖v - e‖ + ‖n‖ := norm_sub_le _ _
      _ ≤ ‖v‖ + ‖e‖ + ‖n‖ := by gcongr; exact norm_sub_le _ _
  nlinarith

lemma relative_mapping_small {c u x n h h' v e : E} {R α γ : ℝ}
    (hR : 0 < R) (hu : ‖u - c‖ ≤ R) (hx : ‖x - c‖ ≤ 2 * R)
    (hn : ∀ w : E, ‖w - c‖ ≤ 2 * R → ⟪n, w - x⟫ ≤ 0)
    (hh : 0 ≤ ⟪h', x - u⟫) (he : ‖e‖ ≤ α * ‖h‖)
    (hgrad : ‖h' - h‖ ≤ γ * ‖v‖) (hv : v = h + e + n)
    (hα : α ≤ 1 / 100) (hγ : γ ≤ 1 / 4) : ‖h‖ ≤ 5 * ‖v‖ := by
  have hb := relative_mapping_bound hR hu hx hn hh he hgrad hv
  have h1 := mul_le_mul_of_nonneg_right hα (norm_nonneg h)
  have h2 := mul_le_mul_of_nonneg_right hγ (norm_nonneg v)
  nlinarith [norm_nonneg h, norm_nonneg v]

lemma projected_descent {c u x y n h h' v e : E} {R α γ η fy fx : ℝ}
    (hR : 0 < R) (hu : ‖u - c‖ ≤ R) (hx : ‖x - c‖ ≤ 2 * R)
    (hy : ‖y - c‖ ≤ 2 * R)
    (hn : ∀ w : E, ‖w - c‖ ≤ 2 * R → ⟪n, w - x⟫ ≤ 0)
    (hh : 0 ≤ ⟪h', x - u⟫) (he : ‖e‖ ≤ α * ‖h‖)
    (hgrad : ‖h' - h‖ ≤ γ * ‖v‖) (hv : v = h + e + n)
    (hα : α ≤ 1 / 100) (hγ : γ ≤ 1 / 4) (hη : 0 < η)
    (hxy : y - x = η • v)
    (hupper : fx ≤ fy - η * ⟪h, v⟫ + η / 8 * ‖v‖ ^ 2) :
    fx ≤ fy - η / 64 * ‖h‖ ^ 2 := by
  have hm := relative_mapping_small hR hu hx hn hh he hgrad hv hα hγ
  have hnv : ⟪n, v⟫ ≤ 0 := by
    have hi := hn y hy
    rw [hxy, inner_smul_right] at hi
    nlinarith
  have he' : ‖e‖ ≤ ‖v‖ / 20 := by
    have h1 := mul_le_mul_of_nonneg_right hα (norm_nonneg h)
    linarith
  have hev : ⟪e, v⟫ ≤ ‖v‖ ^ 2 / 20 := by
    have h1 := real_inner_le_norm e v
    have h2 := mul_le_mul_of_nonneg_right he' (norm_nonneg v)
    nlinarith
  have hid : ‖v‖ ^ 2 = ⟪h, v⟫ + ⟪e, v⟫ + ⟪n, v⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rw 1 [hv]
    rw [inner_add_left, inner_add_left]
  have hlow : 9 / 10 * ‖v‖ ^ 2 ≤ ⟪h, v⟫ := by nlinarith [sq_nonneg ‖v‖]
  have hs : ‖h‖ ^ 2 ≤ 25 * ‖v‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm)
      (show 0 ≤ 5 * ‖v‖ + ‖h‖ by positivity)]
  have h1 := mul_le_mul_of_nonneg_left hlow hη.le
  have h2 := mul_le_mul_of_nonneg_left hs hη.le
  nlinarith [mul_nonneg hη.le (sq_nonneg ‖v‖)]

end OracleTemplate.RelativeGeneralized
