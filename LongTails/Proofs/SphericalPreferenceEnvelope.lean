import LongTails.Setups.SphericalRandomUtility
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Support

open MeasureTheory Set Metric NormedSpace
open scoped RealInnerProductSpace ENNReal

namespace LongTails.Proofs.SphericalPreferenceEnvelope

open LongTails.Setups.SphericalRandomUtility

lemma good_closed (p : Params) (f : Point p.d → ℝ) : IsClosed (good p f) := by
  change IsClosed {z | ∀ x : Feasible p, ∀ y : Feasible p, _}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro y
  apply isClosed_le _ continuous_const
  unfold sampleUtility
  fun_prop

lemma exists_antipodal_good (p : Params) (f : Point p.d → ℝ)
    (μ : Measure (Point p.d)) [IsProbabilityMeasure μ] (hs : Spherical μ)
    (hdim : 2 ≤ p.d) (hq : (1 / 2 : ℝ≥0∞) ≤ μ (good p f)) :
    ∃ z, z ∈ good p f ∧ -z ∈ good p f := by
  let U := (LinearIsometryEquiv.neg ℝ : Point p.d ≃ₗᵢ[ℝ] Point p.d)
  have hm := (good_closed p f).measurableSet
  have he : μ (U ⁻¹' good p f) = μ (good p f) := by
    rw [← Measure.map_apply U.continuous.measurable hm, hs U]
  by_contra h
  have hd : Disjoint (good p f) (U ⁻¹' good p f) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact h ⟨z, hz, hz'⟩
  have hc := (good_closed p f).union ((good_closed p f).preimage U.continuous)
  have hone : μ (good p f ∪ U ⁻¹' good p f) = 1 := by
    apply le_antisymm (prob_le_one)
    rw [measure_union hd (U.continuous.measurable hm), he]
    exact (ENNReal.add_halves 1).ge.trans (add_le_add hq hq)
  have hsub := Measure.support_subset_of_isClosed hc ((mem_ae_iff_prob_eq_one hc.measurableSet).2 hone)
  obtain ⟨z, hz, hsz⟩ := Measure.nonempty_inter_support_of_pos
    (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1 / 2) hq)
  let S := sphere (0 : Point p.d) ‖z‖
  have hsS : S ⊆ μ.support := by
    intro w hw
    have hn : ‖z‖ = ‖w‖ := (mem_sphere_zero_iff_norm.mp hw).symm
    let V := Submodule.reflection (ℝ ∙ (z - w))ᗮ
    have hV : V z = w := Submodule.reflection_sub hn
    rw [Measure.support_eq_forall_isOpen] at hsz ⊢
    intro W hwW hop
    have hpos := hsz (V ⁻¹' W) (by simpa [hV] using hwW) (hop.preimage V.continuous)
    rwa [← Measure.map_apply V.continuous.measurable hop.measurableSet, hs V] at hpos
  have hdim' : 1 < Module.finrank ℝ (Point p.d) := by simp [Point]; omega
  have hconn := isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank hdim') (0 : Point p.d) ‖z‖
  obtain ⟨v, _, hv, hv'⟩ := isPreconnected_closed_iff.mp hconn _ _ (good_closed p f)
    ((good_closed p f).preimage U.continuous) (hsS.trans hsub)
    ⟨z, by simp, hz⟩ ⟨-z, by simp, by simpa [U] using hz⟩
  exact h ⟨v, hv, hv'⟩

lemma systematic_lipschitz (p : Params) (f : Point p.d → ℝ) {z : Point p.d}
    (hz : z ∈ good p f) (hn : -z ∈ good p f) (x y : Feasible p) :
    |f x - f y| ≤ p.B * ‖(x : Point p.d) - y‖ := by
  have h₁ := abs_le.mp (hz x y)
  have h₂ := abs_le.mp (hn x y)
  simp only [sampleUtility, inner_neg_left] at h₁ h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma good_radius (p : Params) (f : Point p.d → ℝ) (hR : 0 < p.R) (hB : 0 ≤ p.B)
    (hf : ∀ x y : Feasible p, |f x - f y| ≤ p.B * ‖(x : Point p.d) - y‖)
    {z : Point p.d} (hz : z ∈ good p f) : ‖z‖ ≤ 2 * p.B := by
  by_cases h : z = 0
  · simp [h, hB]
  have hR' : 0 < (p.R : ℝ) := by exact_mod_cast hR
  let x : Feasible p := ⟨(p.R : ℝ) • normalize z, by
    simp [norm_smul, norm_normalize h, Real.norm_eq_abs, abs_of_nonneg p.R.coe_nonneg]⟩
  let y : Feasible p := ⟨0, by simp⟩
  have he : ‖(x : Point p.d) - y‖ = p.R := by
    simp [x, y, norm_smul, norm_normalize h, Real.norm_eq_abs, abs_of_nonneg p.R.coe_nonneg]
  have hi : ⟪z, normalize z⟫ = ‖z‖ := by
    simp [NormedSpace.normalize, real_inner_smul_right, pow_two, norm_ne_zero_iff.mpr h]
  have ha := (abs_le.mp (hf x y)).1
  have hb := (abs_le.mp (hz x y)).2
  rw [he] at ha hb
  simp only [sampleUtility, x, y, inner_zero_right, add_zero, real_inner_smul_right, hi] at hb
  exact le_of_mul_le_mul_left (by linarith only [ha, hb]) hR'

lemma objective_extension (p : Params) (f : Point p.d → ℝ)
    (μ : Measure (Point p.d)) [IsProbabilityMeasure μ] (hs : Spherical μ)
    (hdim : 2 ≤ p.d) (hR : 0 < p.R) (hB : 0 ≤ p.B) (hq : (1 / 2 : ℝ≥0∞) ≤ μ (good p f))
    (hc : ConvexOn ℝ (closedBall (0 : Point p.d) p.R) f) :
    1 / 2 ≤ μ.real (closedBall 0 (2*p.B)) ∧
      ∃ F : Point p.d → ℝ, LipschitzWith ⟨p.B,hB⟩ F ∧
        EqOn f F (closedBall 0 p.R) ∧ ConvexOn ℝ (closedBall 0 p.R) F ∧
        ∃ o : Feasible p, IsMinOn F (closedBall 0 p.R) o.val := by
  obtain ⟨z, hz, hn⟩ := exists_antipodal_good p f μ hs hdim hq
  have hl := systematic_lipschitz p f hz hn
  have hr := measure_mono (μ := μ) (show good p f ⊆ closedBall 0 (2*p.B) from
    fun v hv => mem_closedBall_zero_iff.mpr (good_radius p f hR hB hl hv))
  have hq' := (ENNReal.toReal_le_toReal (by norm_num : (1/2 : ℝ≥0∞) ≠ ∞) (measure_ne_top _ _)).mpr (hq.trans hr)
  refine ⟨by simpa [measureReal_def] using hq', ?_⟩
  have hL : LipschitzOnWith ⟨p.B,hB⟩ f (closedBall 0 p.R) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [Real.dist_eq, dist_eq_norm]
    exact hl ⟨x,hx⟩ ⟨y,hy⟩
  obtain ⟨F, hF, he⟩ := hL.extend_real
  obtain ⟨o, ho, hmin⟩ := (isCompact_closedBall (0 : Point p.d) p.R).exists_isMinOn
    ⟨0, by simp⟩ hF.continuous.continuousOn
  exact ⟨F, hF, he, hc.congr he, ⟨o,ho⟩, hmin⟩

end LongTails.Proofs.SphericalPreferenceEnvelope
