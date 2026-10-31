import LongTails.Proofs.NonsmoothHiddenGeometry
import LongTails.Algorithms.NonsmoothHiddenAveraging
import Mathlib.Topology.Order.IntermediateValue

open Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.NonsmoothHidden

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def hiddenSegment (c : E ≃ₜ E) (x y : E) (t : ℝ) : E :=
  c.symm ((1 - t) • c x + t • c y)

lemma hiddenSegment_zero (c : E ≃ₜ E) (x y : E) : hiddenSegment c x y 0 = x := by
  simp [hiddenSegment]

lemma hiddenSegment_one (c : E ≃ₜ E) (x y : E) : hiddenSegment c x y 1 = y := by
  simp [hiddenSegment]

lemma hiddenSegment_continuous (c : E ≃ₜ E) (x y : E) : Continuous (hiddenSegment c x y) := by
  unfold hiddenSegment
  exact c.symm.continuous.comp (by fun_prop)

lemma hiddenSegment_value {F H : E → ℝ} {c : E ≃ₜ E}
    (heq : ∀ x, F x = H (c x)) (hH : ConvexOn ℝ univ H)
    (x y : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    F (hiddenSegment c x y t) ≤ (1 - t) * F x + t * F y := by
  have h := hH.2 (mem_univ (c x)) (mem_univ (c y))
    (sub_nonneg.mpr ht.2) ht.1 (by ring : (1 - t) + t = 1)
  simpa only [hiddenSegment, heq, c.apply_symm_apply, smul_eq_mul] using h

lemma hiddenSegment_crosses (c : E ≃ₜ E) {x y : E} {R : ℝ}
    (hx : ‖x‖ ≤ R) (hy : R ≤ ‖y‖) :
    ∃ t ∈ Icc (0 : ℝ) 1, ‖hiddenSegment c x y t‖ = R := by
  have hc := (hiddenSegment_continuous c x y).norm
  apply intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc.continuousOn
  simpa only [hiddenSegment_zero, hiddenSegment_one, mem_Icc] using And.intro hx hy

lemma minimizer_inside_barrier {F H : E → ℝ} {c : E ≃ₜ E} {R : ℝ}
    (hR : 0 < R) (heq : ∀ x, F x = H (c x)) (hH : ConvexOn ℝ univ H)
    (hbarrier : ∀ y, ‖y‖ = R → F 0 ≤ F y) (hmin : ∃ xstar, IsMinOn F univ xstar) :
    ∃ xstar, ‖xstar‖ ≤ R ∧ IsMinOn F univ xstar := by
  obtain ⟨xstar, hstar⟩ := hmin
  by_cases he : F 0 = F xstar
  · refine ⟨0, by simpa using hR.le, ?_⟩
    intro y hy
    rw [he]
    exact hstar hy
  have hg : F xstar < F 0 := lt_of_le_of_ne (hstar (mem_univ 0)) (Ne.symm he)
  by_cases hx : ‖xstar‖ ≤ R
  · exact ⟨xstar, hx, hstar⟩
  have hlarge : R ≤ ‖xstar‖ := (lt_of_not_ge hx).le
  obtain ⟨t, ht, hcross⟩ := hiddenSegment_crosses c (x := 0)
    (by simpa using hR.le) hlarge
  have htpos : 0 < t := by
    by_contra hn
    have htzero : t = 0 := le_antisymm (le_of_not_gt hn) ht.1
    rw [htzero, hiddenSegment_zero, norm_zero] at hcross
    linarith
  have hv := hiddenSegment_value heq hH 0 xstar ht
  have hb := hbarrier _ hcross
  nlinarith [mul_pos htpos (sub_pos.mpr hg)]

omit [InnerProductSpace ℝ E] in
lemma restartOutside_mem {R : ℝ} (hR : 0 ≤ R) (x : E) : ‖restartOutside R x‖ ≤ R := by
  unfold restartOutside
  split_ifs with h
  · simpa using hR
  · exact (lt_of_not_ge h).le

lemma restartOutside_value {F H : E → ℝ} {c : E ≃ₜ E} {R : ℝ}
    (heq : ∀ x, F x = H (c x)) (hH : ConvexOn ℝ univ H)
    (hbarrier : ∀ y, ‖y‖ = R → F 0 ≤ F y) {xstar : E}
    (hstar : IsMinOn F univ xstar) (hxstar : ‖xstar‖ ≤ R) (x : E) :
    F (restartOutside R x) ≤ F x := by
  unfold restartOutside
  split_ifs with hx
  · obtain ⟨t, ht, hcross⟩ := hiddenSegment_crosses c hxstar hx
    have hv := hiddenSegment_value heq hH xstar x ht
    have hb := hbarrier _ hcross
    have hm := hstar (mem_univ x)
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hm)]
  · exact le_rfl

lemma hiddenSegment_distance {c : E ≃ₜ E} {μ Lc R t : ℝ} (hμ : 0 < μ)
    (hLc : 0 ≤ Lc) (ht : 0 ≤ t)
    (hlower : ∀ x y, μ * ‖x - y‖ ≤ ‖c x - c y‖)
    (hupper : ∀ x y, ‖c x - c y‖ ≤ Lc * ‖x - y‖)
    {b u : E} (hb : ‖b‖ ≤ R) (hu : ‖u‖ ≤ R) :
    ‖hiddenSegment c b u t - b‖ ≤ 2 * t * Lc * R / μ := by
  have hn : ‖u - b‖ ≤ 2 * R := by
    have hh := norm_sub_le u b
    linarith
  have he : c (hiddenSegment c b u t) - c b = t • (c u - c b) := by
    simp only [hiddenSegment, c.apply_symm_apply, smul_sub, sub_smul, one_smul]
    abel
  have h := hlower (hiddenSegment c b u t) b
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at h
  apply (le_div_iff₀ hμ).2
  have hh := (hupper u b).trans (mul_le_mul_of_nonneg_left hn hLc)
  nlinarith [mul_le_mul_of_nonneg_left hh ht]

lemma hiddenSegment_contraction {F H : E → ℝ} {c : E ≃ₜ E}
    (heq : ∀ x, F x = H (c x)) (hH : ConvexOn ℝ univ H)
    (b u : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    F (hiddenSegment c b u t) - F u ≤ (1 - t) * (F b - F u) := by
  have h := hiddenSegment_value heq hH b u ht
  linarith

end OracleTemplate.NonsmoothHidden
