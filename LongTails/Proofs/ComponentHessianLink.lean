import LongTails.Proofs.RelativeHessianGate

namespace LongTails.Proofs.ComponentHessianLink

open RelativeHessianGate

noncomputable def link (t : ℝ) : ℝ := spline 5 (40 * t - 4) / 4800

lemma link_smooth : ContDiff ℝ 3 link := by
  have hs : ContDiff ℝ 3 (spline 5) := (spline_contDiff 4).of_le (by norm_num)
  unfold link
  fun_prop

lemma link_hasDerivAt (t : ℝ) : HasDerivAt link (gate t) t := by
  have h := (((spline_hasDerivAt 3 (40 * t - 4)).comp t
    (((hasDerivAt_id t).const_mul 40).sub_const 4))).div_const 4800
  convert h using 1
  · rfl
  · simp [gate]
    ring

lemma link_flat {t : ℝ} (h : t ≤ 1 / 10) : link t = 0 := by
  simp [link, spline_zero (by decide : 5 ≠ 0) (show 40 * t - 4 ≤ 0 by linarith)]

lemma link_tail {t : ℝ} (ht : 1 / 5 ≤ t) : link t = t - 3 / 20 := by
  have h : 4 ≤ 40 * t - 4 := by linarith
  unfold link spline positivePower
  repeat' rw [max_eq_left (by linarith)]
  ring

lemma link_monotone : Monotone link :=
  monotone_of_hasDerivAt_nonneg link_hasDerivAt (fun t => (gate_bounds t).1)

lemma link_nonneg (t : ℝ) : 0 ≤ link t := by
  by_cases h : t ≤ 1 / 10
  · rw [link_flat h]
  · have := link_monotone (show (0 : ℝ) ≤ t by linarith)
    rwa [link_flat (by norm_num : (0 : ℝ) ≤ 1 / 10)] at this

lemma link_ge (t : ℝ) : t - 1 ≤ link t := by
  by_cases h : 1 / 5 ≤ t
  · rw [link_tail h]
    linarith
  · linarith [link_nonneg t]

lemma link_le (t : ℝ) : link t ≤ |t| := by
  by_cases h : t ≤ 1 / 10
  · rw [link_flat h]
    exact abs_nonneg _
  · have hm : Monotone (fun x : ℝ => x - link x) :=
      monotone_of_hasDerivAt_nonneg
        (fun x => (hasDerivAt_id x).sub (link_hasDerivAt x))
        (fun x => sub_nonneg.mpr (gate_bounds x).2)
    have hh := hm (show (0 : ℝ) ≤ t by linarith)
    simp only [link_flat (by norm_num : (0 : ℝ) ≤ 1 / 10), sub_zero] at hh
    linarith [le_abs_self t]

end LongTails.Proofs.ComponentHessianLink
