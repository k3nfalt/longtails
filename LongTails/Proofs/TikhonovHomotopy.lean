import LongTails.Proofs.StiffNewtonStage
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.Connected.Clopen

open scoped RealInnerProductSpace
open Filter Topology Set

namespace LongTails.Proofs.TikhonovHomotopy

open LongTails.Proofs.MonotoneTensorBounds LongTails.Proofs.StiffNewtonStage

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : E → E} {L : ℝ}

lemma _root_.LongTails.Proofs.MonotoneTensorBounds.Regular.zero_exists [FiniteDimensional ℝ E] (h : Regular F L) {b : ℝ} (hb : 0 < b)
    (v : E) : ∃ z, resid F b v z = 0 := by
  set G : E → E := fun z => b • F z + z with hG
  have hcont : Continuous (fderiv ℝ F) := h.smooth.continuous_fderiv (by norm_num)
  have hderiv : ∀ z, HasFDerivAt G (b • fderiv ℝ F z + ContinuousLinearMap.id ℝ E) z :=
    fun z => ((h.hasFDerivAt z).const_smul b).add (hasFDerivAt_id z)
  have hstrict : ∀ z, HasStrictFDerivAt G (b • fderiv ℝ F z + ContinuousLinearMap.id ℝ E) z := by
    intro z
    refine hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
      (Eventually.of_forall hderiv) ?_
    exact ((hcont.const_smul b).add continuous_const).continuousAt
  have hsurj : ∀ z, (b • fderiv ℝ F z + ContinuousLinearMap.id ℝ E).range = ⊤ := by
    intro z
    have hs := h.op_surjective hb.le z
    rw [LinearMap.range_eq_top]
    intro w
    obtain ⟨u, hu⟩ := hs w
    refine ⟨u, ?_⟩
    rw [← hu]
    simp only [op, ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
      LinearMap.add_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      add_apply, smul_apply,
      ContinuousLinearMap.id_apply]
    abel
  have hopen : IsOpen (range G) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨z, rfl⟩
    rw [← (hstrict z).map_nhds_eq_of_surj (hsurj z)]
    exact range_mem_map
  have hexpand : ∀ y y', ‖y - y'‖ ≤ ‖G y - G y'‖ := by
    intro y y'
    have hm := h.mono y y'
    have hinner : ‖y - y'‖ ^ 2 ≤ ⟪G y - G y', y - y'⟫ := by
      have : G y - G y' = b • (F y - F y') + (y - y') := by
        simp only [hG, smul_sub]; abel
      rw [this, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      nlinarith [mul_nonneg hb.le hm]
    have h2 := real_inner_le_norm (G y - G y') (y - y')
    rcases eq_or_lt_of_le (norm_nonneg (y - y')) with h0 | h0
    · rw [← h0]; exact norm_nonneg _
    · nlinarith
  have hGcont : Continuous G :=
    ((h.smooth.continuous).const_smul b).add continuous_id
  have hclosed : IsClosed (range G) := by
    refine isClosed_of_closure_subset fun u hu => ?_
    obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.mp hu
    choose y hy using hs
    have hcauchy : CauchySeq y := by
      have hc : CauchySeq (fun n => G (y n)) := by
        simpa only [hy] using hlim.cauchySeq
      rw [Metric.cauchySeq_iff] at hc ⊢
      intro δ hδ
      obtain ⟨M, hM⟩ := hc δ hδ
      refine ⟨M, fun n hn k hk => ?_⟩
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (hexpand _ _) (by rw [← dist_eq_norm]; exact hM n hn k hk)
    obtain ⟨y0, hy0⟩ := cauchySeq_tendsto_of_complete hcauchy
    have h1 : Tendsto (fun n => G (y n)) atTop (𝓝 (G y0)) := (hGcont.tendsto y0).comp hy0
    have h2 : Tendsto (fun n => G (y n)) atTop (𝓝 u) := by simpa only [hy] using hlim
    exact ⟨y0, tendsto_nhds_unique h1 h2⟩
  have huniv : range G = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨G 0, 0, rfl⟩
  have hw : v ∈ range G := by rw [huniv]; trivial
  obtain ⟨z, hz⟩ := hw
  exact ⟨z, by simp only [resid]; rw [← hz]; simp [hG]⟩

lemma path_mono (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) {a b1 b2 : ℝ} (hb1 : 0 < b1)
    (h12 : b1 ≤ b2) {c w z1 z2 : E}
    (hz1 : resid F b1 (c + (b1 / a) • (w - c)) z1 = 0)
    (hz2 : resid F b2 (c + (b2 / a) • (w - c)) z2 = 0) :
    ‖z1 - c‖ ≤ ‖z2 - c‖ := by
  have hb2 : 0 < b2 := hb1.trans_le h12
  simp only [resid, sub_eq_zero] at hz1 hz2
  set x := z1 - c
  set y := z2 - c
  have e1 : b1 • F z1 = (b1 / a) • (w - c) - x := by
    have : b1 • F z1 = (b1 • F z1 + z1) - z1 := by abel
    rw [this, hz1]; simp only [x]; abel
  have e2 : b2 • F z2 = (b2 / a) • (w - c) - y := by
    have : b2 • F z2 = (b2 • F z2 + z2) - z2 := by abel
    rw [this, hz2]; simp only [y]; abel
  have key : (b1 * b2) • (F z2 - F z1) = b2 • x - b1 • y := by
    have : (b1 * b2) • (F z2 - F z1) = b1 • (b2 • F z2) - b2 • (b1 • F z1) := by
      rw [smul_sub, mul_smul, mul_comm b1 b2, mul_smul]
    rw [this, e1, e2]
    module
  have hdiff : z2 - z1 = y - x := by simp only [x, y]; abel
  have hm := hmono z2 z1
  have hm2 : 0 ≤ ⟪b2 • x - b1 • y, y - x⟫ := by
    rw [← key, ← hdiff, real_inner_smul_left]
    exact mul_nonneg (mul_pos hb1 hb2).le hm
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_self_eq_norm_sq,
    real_inner_comm x y] at hm2
  have hxy := real_inner_le_norm x y
  by_contra hlt'
  have hlt : ‖y‖ < ‖x‖ := lt_of_not_ge hlt'
  have hy0 := norm_nonneg y
  have hpos : 0 < b2 * ‖x‖ - b1 * ‖y‖ := by
    nlinarith [mul_le_mul_of_nonneg_right h12 (norm_nonneg x), mul_lt_mul_of_pos_left hlt hb1]
  nlinarith [mul_pos (sub_pos.mpr hlt) hpos, mul_le_mul_of_nonneg_left hxy (by linarith : (0 : ℝ) ≤ b1 + b2)]

lemma path_step {a b1 b2 : ℝ} (hb2 : 0 < b2) {c w z1 z2 : E}
    (hz1 : resid F b1 (c + (b1 / a) • (w - c)) z1 = 0)
    (hz2 : resid F b2 (c + (b2 / a) • (w - c)) z2 = 0) :
    b1 • (F z2 - F z1) + (z2 - z1) = (1 - b1 / b2) • (z2 - c) := by
  simp only [resid, sub_eq_zero] at hz1 hz2
  have e2 : (b1 / b2) • (b2 • F z2 + z2) = (b1 / b2) • (c + (b2 / a) • (w - c)) := by rw [hz2]
  simp only [smul_add, smul_smul] at e2
  rw [div_mul_cancel₀ _ hb2.ne', show b1 / b2 * (b2 / a) = b1 / a by field_simp] at e2
  have : b1 • (F z2 - F z1) + (z2 - z1) = b1 • F z2 + (b1 / b2) • z2 - (b1 • F z1 + z1) +
      (1 - b1 / b2) • z2 := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [this, e2, hz1]
  module

lemma first_step {a b0 : ℝ} (ha : 0 < a) {c w z0 : E}
    (hz0 : resid F b0 (c + (b0 / a) • (w - c)) z0 = 0) :
    b0 • (F z0 - F c) + (z0 - c) = -((b0 / a) • (a • F c + c - w)) := by
  simp only [resid, sub_eq_zero] at hz0
  have : b0 • (F z0 - F c) + (z0 - c) = (b0 • F z0 + z0) - c - b0 • F c := by
    rw [smul_sub]; abel
  rw [this, hz0]
  have : (b0 / a) • (a • F c) = b0 • F c := by rw [smul_smul, div_mul_cancel₀ _ ha.ne']
  have e3 : (b0 / a) • (a • F c + c - w) = b0 • F c + (b0 / a) • c - (b0 / a) • w := by
    rw [smul_sub, smul_add, this]
  rw [e3]
  module

lemma _root_.LongTails.Proofs.MonotoneTensorBounds.Regular.step_bound (h : Regular F L) {b b2 Q : ℝ} (hb : 0 < b) (hbb : b ≤ b2)
    (hbb' : b2 ≤ 2 * b) {z1 z2 q : E} (heq : b • (F z2 - F z1) + (z2 - z1) = q)
    (hQ : ‖q‖ ≤ Q) (hsmall : 22 * b2 * L * Q ^ 2 ≤ 1) :
    ‖z2 - z1‖ ≤ Q ∧ nq F b2 z2 (z2 - z1) ≤ 5 * Q ^ 2 := by
  set Δ := z2 - z1
  have hinner : ‖Δ‖ ^ 2 + b * ⟪F z2 - F z1, Δ⟫ = ⟪q, Δ⟫ := by
    rw [← heq, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]; ring
  have hqΔ : ⟪q, Δ⟫ ≤ Q * ‖Δ‖ := (real_inner_le_norm q Δ).trans (by gcongr)
  have hmono := h.mono z2 z1
  have hn0 := norm_nonneg Δ
  have hQ0 : 0 ≤ Q := (norm_nonneg q).trans hQ
  have hΔ : ‖Δ‖ ≤ Q := by
    have : ‖Δ‖ ^ 2 ≤ Q * ‖Δ‖ := by nlinarith [mul_nonneg hb.le hmono]
    rcases eq_or_lt_of_le hn0 with h0 | h0
    · rw [← h0]; exact hQ0
    · nlinarith
  refine ⟨hΔ, ?_⟩
  set s := sn F z2 Δ
  have hs0 : 0 ≤ s := sn_nonneg z2 Δ
  have hssq : s ^ 2 = ⟪fderiv ℝ F z2 Δ, Δ⟫ := h.sn_sq z2 Δ
  have hT := h.taylor z2 z1
  have hz : z1 - z2 = -Δ := by simp [Δ]
  rw [hz, norm_neg] at hT
  set B := fderiv ℝ (fderiv ℝ F) z2
  set T := F z1 - F z2 - fderiv ℝ F z2 (-Δ) - (1 / 2 : ℝ) • B (-Δ) (-Δ)
  have hdiff : F z2 - F z1 = fderiv ℝ F z2 Δ - (1 / 2 : ℝ) • B Δ Δ - T := by
    simp only [T, map_neg, neg_apply, neg_neg]; abel
  have htb := h.tensor_bound z2 Δ Δ Δ
  have hTΔ : |⟪T, Δ⟫| ≤ L * ‖Δ‖ ^ 4 := by
    calc |⟪T, Δ⟫| ≤ ‖T‖ * ‖Δ‖ := abs_real_inner_le_norm _ _
      _ ≤ L * ‖Δ‖ ^ 3 * ‖Δ‖ := by gcongr
      _ = L * ‖Δ‖ ^ 4 := by ring
  have hlow : s ^ 2 / 2 - (11 / 2) * L * ‖Δ‖ ^ 4 ≤ ⟪F z2 - F z1, Δ⟫ := by
    rw [hdiff]
    simp only [inner_sub_left, real_inner_smul_left]
    rw [← hssq]
    have hB : ⟪B Δ Δ, Δ⟫ ≤ 6 * Real.sqrt L * ‖Δ‖ ^ 2 * s := by
      rw [real_inner_comm]
      have := (le_abs_self _).trans htb
      nlinarith [this]
    have hsL := Real.sqrt_nonneg L
    have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt h.nonneg
    have hamgm : 3 * Real.sqrt L * ‖Δ‖ ^ 2 * s ≤ s ^ 2 / 2 + (9 / 2) * L * ‖Δ‖ ^ 4 := by
      have h0 := sq_nonneg (s - 3 * Real.sqrt L * ‖Δ‖ ^ 2)
      have e : (s - 3 * Real.sqrt L * ‖Δ‖ ^ 2) ^ 2 =
          s ^ 2 - 6 * Real.sqrt L * ‖Δ‖ ^ 2 * s + 9 * Real.sqrt L ^ 2 * ‖Δ‖ ^ 4 := by ring
      rw [e, hsq] at h0
      linarith
    have := (le_abs_self ⟪T, Δ⟫).trans hTΔ
    nlinarith
  have hmain : ‖Δ‖ ^ 2 + b / 2 * s ^ 2 ≤ Q * ‖Δ‖ + (11 / 2) * b * L * ‖Δ‖ ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hlow hb.le]
  have hnq : nq F b2 z2 Δ = ‖Δ‖ ^ 2 + b2 * s ^ 2 := by unfold nq; rw [hssq]
  rw [hnq]
  have hΔ2 : ‖Δ‖ ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ hn0 hΔ 2
  have hΔ4 : ‖Δ‖ ^ 4 ≤ Q ^ 2 * ‖Δ‖ ^ 2 := by nlinarith [sq_nonneg ‖Δ‖]
  have hb2s : b2 * s ^ 2 ≤ 2 * b * s ^ 2 := by nlinarith [sq_nonneg s]
  have hL0 := h.nonneg
  have h22 : 22 * b * L * Q ^ 2 ≤ 1 := by nlinarith [mul_nonneg hL0 (sq_nonneg Q)]
  nlinarith [mul_le_mul_of_nonneg_left hΔ4 (by positivity : (0 : ℝ) ≤ b * L),
    mul_le_mul_of_nonneg_right hΔ hQ0]

lemma _root_.LongTails.Proofs.MonotoneTensorBounds.Regular.jac_growth (h : Regular F L) (x y : E) :
    ‖fderiv ℝ F y‖ ≤ 2 * ‖fderiv ℝ F x‖ + 10 * L * ‖y - x‖ ^ 2 := by
  set J := fderiv ℝ F x
  set B := fderiv ℝ (fderiv ℝ F) x
  set H := ‖J‖
  have hsH := Real.sqrt_nonneg H
  have hsL := Real.sqrt_nonneg L
  have hB : ‖B‖ ≤ 6 * Real.sqrt L * Real.sqrt H := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun hv => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun k => ?_
    set u := B hv k
    have htb := h.tensor_bound x u hv k
    have s1 := sn_le (F := F) x u
    have s2 := sn_le (F := F) x hv
    have s3 := sn_le (F := F) x k
    have hle : ‖u‖ ^ 2 ≤ 6 * Real.sqrt L * Real.sqrt H * ‖hv‖ * ‖k‖ * ‖u‖ := by
      rw [← real_inner_self_eq_norm_sq]
      refine (le_abs_self _).trans (htb.trans ?_)
      have := sn_nonneg (F := F) x u
      have := sn_nonneg (F := F) x hv
      have := sn_nonneg (F := F) x k
      have hu := norm_nonneg u
      have hh := norm_nonneg hv
      have hk := norm_nonneg k
      have e1 : sn F x u * ‖hv‖ * ‖k‖ ≤ Real.sqrt H * ‖u‖ * ‖hv‖ * ‖k‖ := by gcongr
      have e2 : ‖u‖ * sn F x hv * ‖k‖ ≤ ‖u‖ * (Real.sqrt H * ‖hv‖) * ‖k‖ := by gcongr
      have e3 : ‖u‖ * ‖hv‖ * sn F x k ≤ ‖u‖ * ‖hv‖ * (Real.sqrt H * ‖k‖) := by gcongr
      nlinarith
    rcases eq_or_lt_of_le (norm_nonneg u) with h0 | h0
    · rw [← h0]; positivity
    · nlinarith
  have ht := h.jac_taylor x y
  have hJy : ‖fderiv ℝ F y‖ ≤ H + ‖B‖ * ‖y - x‖ + L * ‖y - x‖ ^ 2 := by
    have : fderiv ℝ F y = J + B (y - x) + (fderiv ℝ F y - J - B (y - x)) := by abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl (B.le_opNorm _))) ht
  have hsq : Real.sqrt H ^ 2 = H := Real.sq_sqrt (norm_nonneg _)
  have hsq' : Real.sqrt L ^ 2 = L := Real.sq_sqrt h.nonneg
  have hr := norm_nonneg (y - x)
  have : ‖B‖ * ‖y - x‖ ≤ H + 9 * L * ‖y - x‖ ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt H - 3 * Real.sqrt L * ‖y - x‖),
      mul_le_mul_of_nonneg_right hB hr]
  linarith

lemma _root_.LongTails.Proofs.MonotoneTensorBounds.Regular.lipschitz_on_ball (h : Regular F L) {xc : E} {r H : ℝ}
    (hH : ∀ y ∈ Metric.closedBall xc r, ‖fderiv ℝ F y‖ ≤ H) {y y' : E}
    (hy : y ∈ Metric.closedBall xc r) (hy' : y' ∈ Metric.closedBall xc r) :
    ‖F y - F y'‖ ≤ H * ‖y - y'‖ :=
  (convex_closedBall xc r).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (h.hasFDerivAt z).hasFDerivWithinAt) hH hy' hy

end LongTails.Proofs.TikhonovHomotopy
