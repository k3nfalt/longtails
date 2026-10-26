import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Connected.Clopen

open scoped RealInnerProductSpace
open Filter Topology Set

namespace LongTails.Proofs.FrozenJacobianSplitting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma jacobian_monotone {F : E → E} {J : E →L[ℝ] E} {c : E}
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) (hd : HasFDerivAt F J c) (v : E) :
    0 ≤ ⟪J v, v⟫ := by
  have hline : HasDerivAt (fun t : ℝ => c + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add c
  have hd' : HasFDerivAt F J (c + (0 : ℝ) • v) := by simpa using hd
  have hcomp : HasDerivAt (fun t : ℝ => F (c + t • v)) (J v) 0 :=
    hd'.comp_hasDerivAt (0 : ℝ) hline
  have hφ : HasDerivAt (fun t : ℝ => ⟪F (c + t • v) - F c, v⟫) ⟪J v, v⟫ 0 := by
    have h1 := (hcomp.sub_const (F c)).inner ℝ (hasDerivAt_const (0 : ℝ) v)
    simpa using h1
  have ht := hasDerivAt_iff_tendsto_slope.mp hφ
  have ht' : Tendsto (slope (fun t : ℝ => ⟪F (c + t • v) - F c, v⟫) 0) (𝓝[>] 0)
      (𝓝 ⟪J v, v⟫) := ht.mono_left (nhdsWithin_mono _ (fun t ht => ne_of_gt ht))
  refine ge_of_tendsto ht' ?_
  filter_upwards [self_mem_nhdsWithin] with t (htpos : 0 < t)
  rw [slope_def_field]
  have hmt := hmono (c + t • v) c
  have hsub : c + t • v - c = t • v := by abel
  rw [hsub, real_inner_smul_right] at hmt
  have hnn : 0 ≤ ⟪F (c + t • v) - F c, v⟫ := by
    by_contra hneg
    have hneg' := lt_of_not_ge hneg
    nlinarith
  simp only [zero_smul, add_zero, sub_self, inner_zero_left, sub_zero]
  positivity

lemma op_coercive (J : E →L[ℝ] E) (hJ : ∀ v, 0 ≤ ⟪J v, v⟫) {β τ : ℝ} (hτ : 0 ≤ τ) (v : E) :
    β * ‖v‖ ^ 2 ≤ ⟪(β • ContinuousLinearMap.id ℝ E + τ • J) v, v⟫ := by
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  nlinarith [mul_nonneg hτ (hJ v)]

lemma op_norm_ge (J : E →L[ℝ] E) (hJ : ∀ v, 0 ≤ ⟪J v, v⟫) {β τ : ℝ}
    (hτ : 0 ≤ τ) (v : E) :
    β * ‖v‖ ≤ ‖(β • ContinuousLinearMap.id ℝ E + τ • J) v‖ := by
  have h1 := op_coercive J hJ (β := β) hτ v
  have h2 := real_inner_le_norm ((β • ContinuousLinearMap.id ℝ E + τ • J) v) v
  rcases eq_or_lt_of_le (norm_nonneg v) with h | h
  · rw [← h]; simp
  · nlinarith

lemma op_injective (J : E →L[ℝ] E) (hJ : ∀ v, 0 ≤ ⟪J v, v⟫) {β τ : ℝ} (hβ : 0 < β)
    (hτ : 0 ≤ τ) : Function.Injective (β • ContinuousLinearMap.id ℝ E + τ • J) := by
  intro u v huv
  have h := op_norm_ge J hJ (β := β) hτ (u - v)
  rw [map_sub, huv, sub_self, norm_zero] at h
  have : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

lemma op_surjective [FiniteDimensional ℝ E] (J : E →L[ℝ] E) (hJ : ∀ v, 0 ≤ ⟪J v, v⟫)
    {β τ : ℝ} (hβ : 0 < β) (hτ : 0 ≤ τ) :
    Function.Surjective (β • ContinuousLinearMap.id ℝ E + τ • J) := by
  have hinj := op_injective J hJ hβ hτ
  exact (LinearMap.injective_iff_surjective
    (f := ((β • ContinuousLinearMap.id ℝ E + τ • J : E →L[ℝ] E) : E →ₗ[ℝ] E))).mp hinj

lemma remainder_lipschitz {F : E → E} {DF : E → E →L[ℝ] E} {L : ℝ} (hL0 : 0 ≤ L)
    (hd : ∀ x, HasFDerivAt F (DF x) x) (hL : ∀ x y, ‖DF x - DF y‖ ≤ L * ‖x - y‖)
    (c y y' : E) {r : ℝ} (hy : ‖y - c‖ ≤ r) (hy' : ‖y' - c‖ ≤ r) :
    ‖(F y - DF c y) - (F y' - DF c y')‖ ≤ L * r * ‖y - y'‖ := by
  have hs : Convex ℝ (Metric.closedBall c r) := convex_closedBall c r
  have hf : ∀ x ∈ Metric.closedBall c r,
      HasFDerivWithinAt (fun x => F x - DF c x) (DF x - DF c) (Metric.closedBall c r) x :=
    fun x _ => ((hd x).sub (DF c).hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ x ∈ Metric.closedBall c r, ‖DF x - DF c‖ ≤ L * r := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    exact (hL x c).trans (mul_le_mul_of_nonneg_left hx hL0)
  have := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hf hb
    (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hy')
    (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hy)
  simpa using this

lemma resolvent_exists [FiniteDimensional ℝ E] {F : E → E} {DF : E → E →L[ℝ] E} {L : ℝ}
    (hL0 : 0 ≤ L) (hd : ∀ x, HasFDerivAt F (DF x) x)
    (hL : ∀ x y, ‖DF x - DF y‖ ≤ L * ‖x - y‖)
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) {a : ℝ} (ha : 0 < a) (w : E) :
    ∃ z, a • F z + z = w := by
  set G : E → E := fun z => a • F z + z with hG
  have hcont : Continuous DF := by
    refine Metric.continuous_iff.mpr fun x δ hδ => ⟨δ / (L + 1), by positivity, fun y hy => ?_⟩
    rw [dist_eq_norm] at hy ⊢
    calc ‖DF y - DF x‖ ≤ L * ‖y - x‖ := hL y x
      _ ≤ (L + 1) * ‖y - x‖ := by nlinarith [norm_nonneg (y - x)]
      _ < (L + 1) * (δ / (L + 1)) := by gcongr
      _ = δ := by field_simp
  have hderiv : ∀ z, HasFDerivAt G (a • DF z + ContinuousLinearMap.id ℝ E) z :=
    fun z => ((hd z).const_smul a).add (hasFDerivAt_id z)
  have hstrict : ∀ z, HasStrictFDerivAt G (a • DF z + ContinuousLinearMap.id ℝ E) z := by
    intro z
    refine hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
      (Eventually.of_forall hderiv) ?_
    exact ((hcont.const_smul a).add continuous_const).continuousAt
  have hsurj : ∀ z, (a • DF z + ContinuousLinearMap.id ℝ E).range = ⊤ := by
    intro z
    have hJ := jacobian_monotone hmono (hd z)
    have hs := op_surjective (DF z) hJ (β := 1) (τ := a) one_pos ha.le
    rw [LinearMap.range_eq_top]
    intro v
    obtain ⟨u, hu⟩ := hs v
    refine ⟨u, ?_⟩
    rw [← hu]
    simp only [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
      LinearMap.add_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe, add_apply,
      smul_apply, ContinuousLinearMap.id_apply, one_smul]
    abel
  have hopen : IsOpen (range G) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨z, rfl⟩
    rw [← (hstrict z).map_nhds_eq_of_surj (hsurj z)]
    exact range_mem_map
  have hexpand : ∀ y y', ‖y - y'‖ ≤ ‖G y - G y'‖ := by
    intro y y'
    have hm := hmono y y'
    have hinner : ‖y - y'‖ ^ 2 ≤ ⟪G y - G y', y - y'⟫ := by
      have : G y - G y' = a • (F y - F y') + (y - y') := by
        simp only [hG, smul_sub]; abel
      rw [this, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      nlinarith [mul_nonneg ha.le hm]
    have h2 := real_inner_le_norm (G y - G y') (y - y')
    rcases eq_or_lt_of_le (norm_nonneg (y - y')) with h | h
    · rw [← h]; exact norm_nonneg _
    · nlinarith
  have hGcont : Continuous G := by
    have : Differentiable ℝ F := fun x => (hd x).differentiableAt
    exact (this.continuous.const_smul a).add continuous_id
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
  have hw : w ∈ range G := by rw [huniv]; trivial
  obtain ⟨z, hz⟩ := hw
  exact ⟨z, hz⟩

lemma fbf_identity (p q g : E) (τ : ℝ) :
    ‖p + q - τ • g‖ ^ 2 = ‖p + q‖ ^ 2 - 2 * τ * ⟪g, p⟫ + ‖τ • g - q‖ ^ 2 - ‖q‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm p g, real_inner_comm q g, real_inner_comm q p]
  ring

lemma fbf_step (G A : E → E) (z zs y z1 : E) {τ μ ℓ : ℝ} (hτ : 0 < τ)
    (hz1 : z1 = y - τ • (A y - A z)) (hres : z - z1 = τ • G y) (hGs : G zs = 0)
    (hsm : μ * ‖y - zs‖ ^ 2 ≤ ⟪G y - G zs, y - zs⟫)
    (hlip : ‖A y - A z‖ ≤ ℓ * ‖y - z‖) :
    ‖z1 - zs‖ ^ 2 ≤
      ‖z - zs‖ ^ 2 - 2 * τ * μ * ‖y - zs‖ ^ 2 - (1 - τ ^ 2 * ℓ ^ 2) * ‖z - y‖ ^ 2 := by
  rw [hGs, sub_zero] at hsm
  have e1 : z1 - zs = (y - zs) + (z - y) - τ • G y := by
    have : z1 = z - τ • G y := by rw [← hres]; abel
    rw [this]; abel
  have e2 : τ • G y - (z - y) = τ • (A y - A z) := by
    rw [← hres, hz1]; abel
  have e3 : z - zs = (y - zs) + (z - y) := by abel
  have hsq : ‖τ • G y - (z - y)‖ ^ 2 ≤ τ ^ 2 * ℓ ^ 2 * ‖z - y‖ ^ 2 := by
    rw [e2, norm_smul, Real.norm_eq_abs, abs_of_pos hτ, norm_sub_rev z y]
    have h1 := mul_le_mul_of_nonneg_left hlip hτ.le
    have h2 := pow_le_pow_left₀ (mul_nonneg hτ.le (norm_nonneg _)) h1 2
    nlinarith [h2]
  rw [e1, fbf_identity, e3]
  nlinarith [hsm, hsq]

end LongTails.Proofs.FrozenJacobianSplitting
