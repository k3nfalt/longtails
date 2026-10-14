import LongTails.Proofs.FrankWolfePowerBounds
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Topology.Compactness.Compact

open Set Filter
open scoped Topology

namespace OracleTemplate.FrankWolfe

noncomputable def curvatureSlope (q w : ℝ) : ℝ :=
  -dslope (fun z : ℝ => (1 + z) ^ (-1 / q)) 0 w

lemma curvatureSlope_zero (q : ℝ) : curvatureSlope q 0 = 1 / q := by
  have hd : HasDerivAt (fun z : ℝ => (1 + z) ^ (-1 / q)) (-1 / q) 0 := by
    convert ((hasDerivAt_const (0 : ℝ) 1).add (hasDerivAt_id 0)).rpow_const
      (p := -1 / q) (Or.inl (by norm_num)) using 1 <;> simp
  simp only [curvatureSlope, dslope_same, hd.deriv]
  ring

lemma curvatureSlope_continuous (q : ℝ) : ContinuousAt (curvatureSlope q) 0 := by
  apply ContinuousAt.neg
  apply continuousAt_dslope_same.mpr
  exact (((hasDerivAt_const (0 : ℝ) 1).add (hasDerivAt_id 0)).rpow_const
    (p := -1 / q) (Or.inl (by norm_num))).differentiableAt

lemma curvatureSlope_identity (q w : ℝ) :
    w * curvatureSlope q w = 1 - (1 + w) ^ (-1 / q) := by
  have h := sub_smul_dslope (fun z : ℝ => (1 + z) ^ (-1 / q)) 0 w
  simp only [sub_zero, smul_eq_mul, add_zero, Real.one_rpow] at h
  dsimp [curvatureSlope]
  nlinarith

noncomputable def limitingMap (q v : ℝ) : ℝ :=
  (q + 1) / q * v ^ (-1 / (q - 1)) - v / q

lemma limitingMap_one {q : ℝ} (hq : q ≠ 0) : limitingMap q 1 = 1 := by
  simp only [limitingMap, Real.one_rpow, mul_one]
  field_simp
  ring

lemma limitingMap_hasDerivAt {q v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (limitingMap q)
      ((q + 1) / q * (-1 / (q - 1)) * v ^ (-1 / (q - 1) - 1) - 1 / q) v := by
  convert (((hasDerivAt_id v).rpow_const (p := -1 / (q - 1))
    (Or.inl hv)).const_mul ((q + 1) / q)).sub ((hasDerivAt_id v).div_const q) using 1
  · funext x
    rfl
  · simp only [id_eq]
    ring

lemma limitingMap_derivative_one {q : ℝ} (hq : 3 < q) :
    HasDerivAt (limitingMap q) (-2 / (q - 1)) 1 := by
  convert limitingMap_hasDerivAt (q := q) (by norm_num : (1 : ℝ) ≠ 0) using 1
  simp only [Real.one_rpow, mul_one]
  field_simp [ne_of_gt (show 0 < q by linarith), ne_of_gt (show 0 < q - 1 by linarith)]
  ring

lemma local_fixed_point_contraction {F : ℝ → ℝ} {a d rate : ℝ}
    (hd : HasDerivAt F d a) (hrate : |d| < rate) :
    ∃ δ > 0, ∀ v, |v - a| ≤ δ → |F v - F a| ≤ rate * |v - a| := by
  have hcont : ContinuousAt (fun v => |dslope F a v|) a :=
    (continuousAt_dslope_same.mpr hd.differentiableAt).abs
  have hbound : ∀ᶠ v in 𝓝 a, |dslope F a v| < rate :=
    hcont.eventually (gt_mem_nhds (by simpa [hd.deriv] using hrate))
  obtain ⟨ε, hε, hεbound⟩ := Metric.eventually_nhds_iff.mp hbound
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro v hv
  have hvε : dist v a < ε := by rw [Real.dist_eq]; linarith
  have hs := hεbound hvε
  have heq := sub_smul_dslope F a v
  rw [smul_eq_mul] at heq
  rw [← heq, abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hs.le (abs_nonneg (v - a))]

lemma compact_strip {a b : ℝ} {P : ℝ → ℝ → Prop}
    (hP : ∀ v ∈ Icc a b, ∀ᶠ z : ℝ × ℝ in 𝓝 (0, v), P z.1 z.2) :
    ∃ δ > 0, ∀ u ∈ Icc (0 : ℝ) δ, ∀ v ∈ Icc a b, P u v := by
  have h := isCompact_Icc.eventually_forall_of_forall_eventually hP
  obtain ⟨ε, hε, hεbound⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro u hu v hv
  apply hεbound _ v hv
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hu.1]
  linarith [hu.2]

lemma invariant_strip {W : ℝ × ℝ → ℝ} {δ rate : ℝ}
    (hδ : 0 < δ) (hrate : rate < 1)
    (hcont : ∀ v ∈ Icc (1 - δ) (1 + δ), ContinuousAt W (0, v))
    (hlim : ∀ v ∈ Icc (1 - δ) (1 + δ), |W (0, v) - 1| ≤ rate * δ) :
    ∃ u0 > 0, ∀ u ∈ Icc (0 : ℝ) u0, ∀ v ∈ Icc (1 - δ) (1 + δ),
      |W (u, v) - 1| ≤ δ := by
  apply compact_strip
  intro v hv
  have hstrict : |W (0, v) - 1| < δ := by
    have := hlim v hv
    nlinarith
  have h := ((hcont v hv).sub_const 1).abs.eventually (gt_mem_nhds hstrict)
  exact h.mono fun z hz => hz.le

end OracleTemplate.FrankWolfe
