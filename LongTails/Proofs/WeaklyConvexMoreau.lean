import LongTails.Setups.WeaklyConvexHeavyTailed
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace OracleTemplate.WeaklyConvexHeavyTailed

open LongTails.Setups.WeaklyConvexHeavyTailed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def WeakSubgradientOn (D : Set E) (ρ : ℝ) (f : E → ℝ) (v : E → E) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, f x + ⟪v x, y - x⟫ - ρ / 2 * ‖y - x‖ ^ 2 ≤ f y

omit [InnerProductSpace ℝ E] in
lemma proxObj_self (f : E → ℝ) (ρ : ℝ) (x : E) : proxObj f ρ x x = f x := by
  simp [proxObj]

lemma weak_segment {D : Set E} (hD : Convex ℝ D) {ρ : ℝ} {f : E → ℝ} {v : E → E}
    (hv : WeakSubgradientOn D ρ f v) {a z : E} (ha : a ∈ D) (hz : z ∈ D)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f (a + t • (z - a)) ≤ (1 - t) * f a + t * f z + ρ / 2 * (t * (1 - t)) * ‖z - a‖ ^ 2 := by
  have hw : a + t • (z - a) ∈ D := hD.add_smul_sub_mem ha hz ⟨ht0, ht1⟩
  have h1 := hv _ hw a ha
  have h2 := hv _ hw z hz
  have hwa : a - (a + t • (z - a)) = (-t) • (z - a) := by module
  have hwz : z - (a + t • (z - a)) = (1 - t) • (z - a) := by module
  rw [hwa, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, neg_sq, inner_smul_right] at h1
  rw [hwz, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inner_smul_right] at h2
  have h3 := add_le_add (mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 1 - t))
    (mul_le_mul_of_nonneg_left h2 ht0)
  nlinarith [h3]

lemma norm_segment_sq (x a z : E) (t : ℝ) :
    ‖a + t • (z - a) - x‖ ^ 2 =
      (1 - t) * ‖a - x‖ ^ 2 + t * ‖z - x‖ ^ 2 - t * (1 - t) * ‖z - a‖ ^ 2 := by
  have h : a + t • (z - a) - x = (1 - t) • (a - x) + t • (z - x) := by module
  have hza : z - a = (z - x) - (a - x) := by abel
  have e1 : ‖(1 - t) • (a - x) + t • (z - x)‖ ^ 2 =
      (1 - t) ^ 2 * ‖a - x‖ ^ 2 + 2 * ((1 - t) * t) * ⟪a - x, z - x⟫ + t ^ 2 * ‖z - x‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow,
      mul_pow, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right]
    ring
  have e2 : ‖(z - x) - (a - x)‖ ^ 2 = ‖z - x‖ ^ 2 - 2 * ⟪a - x, z - x⟫ + ‖a - x‖ ^ 2 := by
    linarith [norm_sub_sq_real (z - x) (a - x), real_inner_comm (a - x) (z - x)]
  rw [h, e1, hza, e2]
  ring

lemma proxObj_segment {D : Set E} (hD : Convex ℝ D) {ρ : ℝ} {f : E → ℝ} {v : E → E}
    (hv : WeakSubgradientOn D ρ f v) (x : E) {a z : E} (ha : a ∈ D) (hz : z ∈ D)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    proxObj f ρ x (a + t • (z - a)) ≤
      (1 - t) * proxObj f ρ x a + t * proxObj f ρ x z - ρ / 2 * (t * (1 - t)) * ‖z - a‖ ^ 2 := by
  unfold proxObj
  have h1 := weak_segment hD hv ha hz ht0 ht1
  rw [norm_segment_sq x a z t]
  nlinarith [h1]

lemma scale_identity {c D : ℝ} (hc : 0 < c) : (1 - (c - D) / (2 * c)) * c = (c + D) / 2 := by
  field_simp
  ring

lemma growth_of_isMinOn {D : Set E} (hD : Convex ℝ D) {ρ : ℝ} {f : E → ℝ} {v : E → E}
    (hv : WeakSubgradientOn D ρ f v) (hρ : 0 < ρ) {x xh : E} (hxh : xh ∈ D)
    (hmin : IsMinOn (proxObj f ρ x) D xh) {z : E} (hz : z ∈ D) :
    proxObj f ρ x xh + ρ / 2 * ‖z - xh‖ ^ 2 ≤ proxObj f ρ x z := by
  have key : ∀ t : ℝ, 0 < t → t < 1 →
      (1 - t) * (ρ / 2 * ‖z - xh‖ ^ 2) ≤ proxObj f ρ x z - proxObj f ρ x xh := by
    intro t ht0 ht1
    have hseg := proxObj_segment hD hv x hxh hz ht0.le ht1.le
    have hmin' : proxObj f ρ x xh ≤ proxObj f ρ x (xh + t • (z - xh)) :=
      hmin (hD.add_smul_sub_mem hxh hz ⟨ht0.le, ht1.le⟩)
    have h3 : t * ((1 - t) * (ρ / 2 * ‖z - xh‖ ^ 2)) ≤
        t * (proxObj f ρ x z - proxObj f ρ x xh) := by nlinarith [hseg, hmin']
    exact le_of_mul_le_mul_left h3 ht0
  have hc0 : 0 ≤ ρ / 2 * ‖z - xh‖ ^ 2 := by positivity
  by_contra hcon
  push Not at hcon
  have hhalf := key (1 / 2) (by norm_num) (by norm_num)
  have hD0 : 0 ≤ proxObj f ρ x z - proxObj f ρ x xh := by nlinarith
  have hcpos : 0 < ρ / 2 * ‖z - xh‖ ^ 2 := by linarith
  have hgap : 0 < ρ / 2 * ‖z - xh‖ ^ 2 - (proxObj f ρ x z - proxObj f ρ x xh) := by linarith
  have ht0 : 0 < (ρ / 2 * ‖z - xh‖ ^ 2 - (proxObj f ρ x z - proxObj f ρ x xh)) /
      (2 * (ρ / 2 * ‖z - xh‖ ^ 2)) := by positivity
  have ht1 : (ρ / 2 * ‖z - xh‖ ^ 2 - (proxObj f ρ x z - proxObj f ρ x xh)) /
      (2 * (ρ / 2 * ‖z - xh‖ ^ 2)) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have h4 := key _ ht0 ht1
  rw [scale_identity hcpos] at h4
  linarith

lemma f_le_of_weak {D : Set E} {ρ G : ℝ} {f : E → ℝ} {v : E → E} (hv : WeakSubgradientOn D ρ f v)
    (hG : ∀ x ∈ D, ‖v x‖ ≤ G) {x y : E} (hx : x ∈ D) (hy : y ∈ D) :
    f y ≤ f x + G * ‖y - x‖ + ρ / 2 * ‖y - x‖ ^ 2 := by
  have h := hv y hy x hx
  have h2 := abs_real_inner_le_norm (v y) (x - y)
  rw [norm_sub_rev x y] at h2 h
  have h3 : ‖v y‖ * ‖y - x‖ ≤ G * ‖y - x‖ :=
    mul_le_mul_of_nonneg_right (hG y hy) (norm_nonneg _)
  have := (abs_le.mp h2).1
  linarith

lemma f_ge_of_weak {D : Set E} {ρ G : ℝ} {f : E → ℝ} {v : E → E} (hv : WeakSubgradientOn D ρ f v)
    (hG : ∀ x ∈ D, ‖v x‖ ≤ G) {x y : E} (hx : x ∈ D) (hy : y ∈ D) :
    f x - G * ‖y - x‖ - ρ / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have h := hv x hx y hy
  have h2 := abs_real_inner_le_norm (v x) (y - x)
  have h3 : ‖v x‖ * ‖y - x‖ ≤ G * ‖y - x‖ :=
    mul_le_mul_of_nonneg_right (hG x hx) (norm_nonneg _)
  have := (abs_le.mp h2).1
  linarith

lemma continuousOn_of_weak {D : Set E} {ρ G : ℝ} {f : E → ℝ} {v : E → E}
    (hv : WeakSubgradientOn D ρ f v) (hG : ∀ x ∈ D, ‖v x‖ ≤ G) (hρ : 0 ≤ ρ) (hG0 : 0 ≤ G) :
    ContinuousOn f D := by
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  refine ⟨min 1 (ε / (G + ρ + 1)), by positivity, fun y hy hxy => ?_⟩
  rw [dist_eq_norm] at hxy
  have hy1 : ‖y - x‖ < 1 := lt_of_lt_of_le hxy (min_le_left _ _)
  have hy2 : ‖y - x‖ < ε / (G + ρ + 1) := lt_of_lt_of_le hxy (min_le_right _ _)
  have hyε : (G + ρ + 1) * ‖y - x‖ < ε := by
    rw [lt_div_iff₀ (by positivity)] at hy2; linarith
  have hsq : ‖y - x‖ ^ 2 ≤ ‖y - x‖ := by nlinarith [norm_nonneg (y - x)]
  have h1 := f_le_of_weak hv hG hx hy
  have h2 := f_ge_of_weak hv hG hx hy
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith [norm_nonneg (y - x)]

lemma exists_prox [FiniteDimensional ℝ E] {D : Set E} (hDc : IsClosed D) {ρ G : ℝ}
    {f : E → ℝ} {v : E → E} (hv : WeakSubgradientOn D ρ f v) (hG : ∀ x ∈ D, ‖v x‖ ≤ G)
    (hρ : 0 < ρ) (hG0 : 0 ≤ G) {xb : E} (hxb : xb ∈ D) (x : E) :
    ∃ xh ∈ D, IsMinOn (proxObj f ρ x) D xh := by
  have hcont : ContinuousOn (proxObj f ρ x) D := by
    unfold proxObj
    exact (continuousOn_of_weak hv hG hρ.le hG0).add
      ((((continuous_id.sub continuous_const).norm.pow 2).const_smul ρ).continuousOn)
  have hK : IsCompact (D ∩ Metric.closedBall xb (2 * G / ρ + 4 * ‖xb - x‖)) :=
    (isCompact_closedBall xb _).inter_left hDc
  obtain ⟨xh, hxh, hmin⟩ := hK.exists_isMinOn
    ⟨xb, hxb, Metric.mem_closedBall_self (by positivity)⟩ (hcont.mono Set.inter_subset_left)
  refine ⟨xh, hxh.1, fun z hz => ?_⟩
  by_cases hzb : z ∈ Metric.closedBall xb (2 * G / ρ + 4 * ‖xb - x‖)
  · exact hmin ⟨hz, hzb⟩
  · have hzR : 2 * G / ρ + 4 * ‖xb - x‖ < ‖z - xb‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hzb
      exact lt_of_not_ge hzb
    have hzx : proxObj f ρ x xb ≤ proxObj f ρ x z := by
      unfold proxObj
      have h2 := f_ge_of_weak hv hG hxb hz
      have hr0 : 0 ≤ ‖z - xb‖ := norm_nonneg _
      have hRr : 2 * G + 4 * ρ * ‖xb - x‖ ≤ ρ * ‖z - xb‖ := by
        have := mul_lt_mul_of_pos_left hzR hρ
        rw [mul_add, mul_div_cancel₀ _ hρ.ne'] at this
        linarith
      have h4d : 4 * ‖xb - x‖ ≤ ‖z - xb‖ := by
        have : ρ * (4 * ‖xb - x‖) ≤ ρ * ‖z - xb‖ := by nlinarith [hRr, hG0]
        exact le_of_mul_le_mul_left this hρ
      have htri : ‖z - xb‖ - ‖xb - x‖ ≤ ‖z - x‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub z x xb
        rw [norm_sub_rev x xb] at this
        linarith
      have hsq : (‖z - xb‖ - ‖xb - x‖) ^ 2 ≤ ‖z - x‖ ^ 2 :=
        pow_le_pow_left₀ (by linarith [norm_nonneg (xb - x)]) htri 2
      have hsqρ := mul_le_mul_of_nonneg_left hsq hρ.le
      have key := mul_le_mul_of_nonneg_right hRr hr0
      nlinarith [hsqρ, key, h2]
    exact (hmin ⟨hxb, Metric.mem_closedBall_self (by positivity)⟩).trans hzx

lemma prox_lipschitz {D : Set E} (hD : Convex ℝ D) {ρ : ℝ} {f : E → ℝ} {v : E → E}
    (hv : WeakSubgradientOn D ρ f v) (hρ : 0 < ρ) {x x' xh xh' : E}
    (hxh : xh ∈ D) (hmin : IsMinOn (proxObj f ρ x) D xh)
    (hxh' : xh' ∈ D) (hmin' : IsMinOn (proxObj f ρ x') D xh') :
    ‖xh - xh'‖ ≤ 2 * ‖x - x'‖ := by
  have h1 := growth_of_isMinOn hD hv hρ hxh hmin hxh'
  have h2 := growth_of_isMinOn hD hv hρ hxh' hmin' hxh
  unfold proxObj at h1 h2
  have n1 := norm_sub_sq_real xh' x
  have n2 := norm_sub_sq_real xh' x'
  have n3 := norm_sub_sq_real xh x'
  have n4 := norm_sub_sq_real xh x
  have n5 : ‖xh' - xh‖ ^ 2 = ‖xh - xh'‖ ^ 2 := by rw [norm_sub_rev]
  have e : ⟪x' - x, xh' - xh⟫ = ⟪xh', x'⟫ - ⟪xh', x⟫ - ⟪xh, x'⟫ + ⟪xh, x⟫ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm xh' x',
      real_inner_comm xh x', real_inner_comm xh' x, real_inner_comm xh x]
    ring
  have hsum' : ρ * ‖xh - xh'‖ ^ 2 ≤
      ρ * (‖xh' - x‖ ^ 2 - ‖xh - x‖ ^ 2 + (‖xh - x'‖ ^ 2 - ‖xh' - x'‖ ^ 2)) := by
    nlinarith [h1, h2, n5]
  have hsum0 := le_of_mul_le_mul_left hsum' hρ
  have hsum : ρ * ‖xh - xh'‖ ^ 2 ≤ ρ * (2 * ⟪x' - x, xh' - xh⟫) := by
    apply mul_le_mul_of_nonneg_left _ hρ.le
    linarith [hsum0, n1, n2, n3, n4, e]
  have hcs : ⟪x' - x, xh' - xh⟫ ≤ ‖x - x'‖ * ‖xh - xh'‖ := by
    have := real_inner_le_norm (x' - x) (xh' - xh)
    rw [norm_sub_rev x' x, norm_sub_rev xh' xh] at this
    exact this
  have h4 : ‖xh - xh'‖ ^ 2 ≤ 2 * (‖x - x'‖ * ‖xh - xh'‖) :=
    (le_of_mul_le_mul_left hsum hρ).trans (by linarith [hcs])
  by_cases hz : ‖xh - xh'‖ = 0
  · rw [hz]; positivity
  · have hpos : 0 < ‖xh - xh'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith [h4]

lemma prox_unique {D : Set E} (hD : Convex ℝ D) {ρ : ℝ} {f : E → ℝ} {v : E → E}
    (hv : WeakSubgradientOn D ρ f v) (hρ : 0 < ρ) {x xh xh' : E}
    (hxh : xh ∈ D) (hmin : IsMinOn (proxObj f ρ x) D xh)
    (hxh' : xh' ∈ D) (hmin' : IsMinOn (proxObj f ρ x) D xh') : xh = xh' := by
  have := prox_lipschitz hD hv hρ hxh hmin hxh' hmin'
  simp only [sub_self, norm_zero, mul_zero] at this
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

lemma inner_weak_prox {D : Set E} (hD : Convex ℝ D) {ρ : ℝ} {f : E → ℝ} {v : E → E}
    (hv : WeakSubgradientOn D ρ f v) (hρ : 0 < ρ) {x xh : E} (hx : x ∈ D)
    (hxh : xh ∈ D) (hmin : IsMinOn (proxObj f ρ x) D xh) :
    ⟪v x, xh - x⟫ ≤ -ρ * ‖xh - x‖ ^ 2 := by
  have h1 := hv x hx xh hxh
  have h2 := growth_of_isMinOn hD hv hρ hxh hmin hx
  rw [proxObj_self] at h2
  unfold proxObj at h2
  have h3 : ‖x - xh‖ ^ 2 = ‖xh - x‖ ^ 2 := by rw [norm_sub_rev]
  rw [h3] at h2
  nlinarith [h1, h2]

lemma prox_dist_le {D : Set E} (hD : Convex ℝ D) {ρ G : ℝ} {f : E → ℝ} {v : E → E}
    (hv : WeakSubgradientOn D ρ f v) (hG : ∀ x ∈ D, ‖v x‖ ≤ G) (hρ : 0 < ρ) {x xh : E}
    (hx : x ∈ D) (hxh : xh ∈ D) (hmin : IsMinOn (proxObj f ρ x) D xh) :
    ‖xh - x‖ ≤ G / ρ := by
  have h1 := inner_weak_prox hD hv hρ hx hxh hmin
  have h2 := abs_real_inner_le_norm (v x) (xh - x)
  have h3 : ‖v x‖ * ‖xh - x‖ ≤ G * ‖xh - x‖ :=
    mul_le_mul_of_nonneg_right (hG x hx) (norm_nonneg _)
  have h4 := (abs_le.mp h2).1
  rw [le_div_iff₀ hρ]
  by_cases hz : ‖xh - x‖ = 0
  · rw [hz]; simp; exact mul_nonneg (le_trans (norm_nonneg _) (hG x hx)) hρ.le |> fun h => by nlinarith [norm_nonneg (v x), hG x hx]
  · have hpos : 0 < ‖xh - x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith [h1, h3, h4]

lemma envelope_step {D : Set E} {f : E → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) {x xh xp xhp : E}
    (hxh : xh ∈ D) (hminp : IsMinOn (proxObj f ρ xp) D xhp) (γ : ℝ) (g : E)
    (hproj : ‖xh - xp‖ ≤ ‖xh - (x - γ • g)‖) :
    proxObj f ρ xp xhp ≤
      proxObj f ρ x xh + 2 * ρ * γ * ⟪g, xh - x⟫ + ρ * γ ^ 2 * ‖g‖ ^ 2 := by
  have h1 : proxObj f ρ xp xhp ≤ proxObj f ρ xp xh := hminp hxh
  refine h1.trans ?_
  unfold proxObj
  have h2 : ‖xh - xp‖ ^ 2 ≤ ‖xh - (x - γ • g)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hproj 2
  have h3 : xh - (x - γ • g) = (xh - x) + γ • g := by abel
  rw [h3, norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right,
    real_inner_comm] at h2
  nlinarith [h2]

end OracleTemplate.WeaklyConvexHeavyTailed
