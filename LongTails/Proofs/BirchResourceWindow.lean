import Mathlib

namespace LongTails.Proofs.BirchResourceWindow

open Finset MeasureTheory Set

lemma interval_integrable (x y c : ℝ) : Integrable ((Ico x y).indicator (fun _ => c)) volume := by
  apply (integrable_indicator_iff measurableSet_Ico).2
  exact integrableOn_const (hs := by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
    (hC := by simp)

lemma interval_integral (x y c : ℝ) (hxy : x ≤ y) :
    (∫ z, (Ico x y).indicator (fun _ => c) z) = (y - x) * c := by
  rw [integral_indicator_const _ measurableSet_Ico, smul_eq_mul, measureReal_def, Real.volume_Ico,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hxy)]

lemma interval_capacity {J : Type*} (s : Finset J) (a b rate : J → ℝ) (T R : ℝ)
    (hT : 0 ≤ T) (htime : ∀ j ∈ s, 0 ≤ a j ∧ a j ≤ b j ∧ b j ≤ T)
    (hcap : ∀ t ∈ Ico (0 : ℝ) T, (∑ j ∈ s,
      (Ico (a j) (b j)).indicator (fun _ => rate j) t) ≤ R) :
    (∑ j ∈ s, (b j - a j) * rate j) ≤ T * R := by
  let f := fun j => (Ico (a j) (b j)).indicator (fun _ : ℝ => rate j)
  let g := (Ico (0 : ℝ) T).indicator (fun _ : ℝ => R)
  have hle (t : ℝ) : (∑ j ∈ s, f j t) ≤ g t := by
    by_cases h : t ∈ Ico (0 : ℝ) T
    · rw [show g t = R from indicator_of_mem h _]
      exact hcap t h
    · rw [show g t = 0 from indicator_of_notMem h _]
      have hz : (∑ j ∈ s, f j t) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        apply indicator_of_notMem
        intro hm
        exact h ⟨(htime j hj).1.trans hm.1, hm.2.trans_le (htime j hj).2.2⟩
      rw [hz]
  have hm := integral_mono (integrable_finsetSum s (fun j _ => interval_integrable (a j) (b j) (rate j)))
    (interval_integrable 0 T R) hle
  rw [integral_finsetSum _ (fun j _ => interval_integrable (a j) (b j) (rate j))] at hm
  change (∑ j ∈ s, ∫ t, f j t) ≤ (∫ t, g t) at hm
  rw [interval_integral 0 T R hT, sub_zero] at hm
  convert hm using 1
  exact sum_congr rfl (fun j hj => (interval_integral (a j) (b j) (rate j) (htime j hj).2.1).symm)

lemma exists_unoccupied {J : Type*} (s : Finset J) (a b : J → ℝ) {T : ℝ}
    (hT : 0 ≤ T) (hab : ∀ j ∈ s, a j ≤ b j)
    (hlen : ∑ j ∈ s, (b j - a j) < T) :
    ∃ t ∈ Ico (0 : ℝ) T, ∀ j ∈ s, t ∉ Ico (a j) (b j) := by
  classical
  by_contra! h
  let f := fun j => (Ico (a j) (b j)).indicator (fun _ : ℝ => (1 : ℝ))
  let g := (Ico (0 : ℝ) T).indicator (fun _ : ℝ => (1 : ℝ))
  have hi (j : J) : Integrable (f j) volume := interval_integrable _ _ _
  have hle (t : ℝ) : g t ≤ ∑ j ∈ s, f j t := by
    have hn (j : J) : 0 ≤ f j t := indicator_nonneg (fun _ _ => zero_le_one) _
    by_cases ht : t ∈ Ico (0 : ℝ) T
    · obtain ⟨j, hj, hmem⟩ := h t ht
      have he : f j t = 1 := indicator_of_mem hmem _
      rw [show g t = 1 from indicator_of_mem ht _, ← he]
      exact single_le_sum (fun j _ => hn j) hj
    · rw [show g t = 0 from indicator_of_notMem ht _]
      exact sum_nonneg (fun j _ => hn j)
  have hh := integral_mono (interval_integrable 0 T 1)
    (integrable_finsetSum s (fun j _ => hi j)) hle
  rw [integral_finsetSum _ (fun j _ => hi j)] at hh
  change (∫ t, g t) ≤ ∑ j ∈ s, ∫ t, f j t at hh
  rw [interval_integral 0 T 1 hT, sub_zero, mul_one] at hh
  have he : (∑ j ∈ s, ∫ t, f j t) = ∑ j ∈ s, (b j - a j) :=
    sum_congr rfl (fun j hj => by rw [interval_integral _ _ _ (hab j hj), mul_one])
  rw [he] at hh
  exact (not_lt_of_ge hh) hlen

end LongTails.Proofs.BirchResourceWindow
