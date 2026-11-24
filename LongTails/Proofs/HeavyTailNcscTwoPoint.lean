import LongTails.Proofs.HeavyTailNcscChain
import LongTails.Proofs.HighProbabilityTwoPointFailure

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HeavyTailNcscTwoPoint

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open LongTails.Setups.HighDimensionalHeavyTailedNcsc
open LongTails.Proofs.HeavyTailNcscChain
open LongTails.Proofs.AbcHardOracle LongTails.Proofs.AbcLowerMeasure
open LongTails.Proofs.HighProbabilityTwoPointFailure (reveal measurable_reveal reveal_integral
  stream_no_reveal measurableSet_no_reveal execute_congr unitVector unitVector_norm
  reveal_integrable)

noncomputable def clip1 (t : ℝ) : ℝ := max (-1) (min 1 t)

noncomputable def hub (t : ℝ) : ℝ := ∫ x in (0 : ℝ)..t, clip1 x

lemma clip1_continuous : Continuous clip1 := by unfold clip1; fun_prop

lemma clip1_lipschitz (s t : ℝ) : |clip1 s - clip1 t| ≤ |s - t| := by
  unfold clip1
  have h1 := abs_max_sub_max_le_max (-1 : ℝ) (min 1 s) (-1) (min 1 t)
  have h2 := abs_min_sub_min_le_max (1 : ℝ) s 1 t
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg (min 1 s - min 1 t))] at h1
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg (s - t))] at h2
  exact h1.trans h2

lemma clip1_abs (t : ℝ) : |clip1 t| ≤ 1 := by
  unfold clip1
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma clip1_zero : clip1 0 = 0 := by norm_num [clip1]

lemma clip1_of_mem {t : ℝ} (h0 : -1 ≤ t) (h1 : t ≤ 1) : clip1 t = t := by
  unfold clip1
  rw [min_eq_right h1, max_eq_right h0]

lemma hub_hasDerivAt (t : ℝ) : HasDerivAt hub (clip1 t) t :=
  (clip1_continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

lemma hub_zero : hub 0 = 0 := by simp [hub]

lemma hub_upper (t t' : ℝ) : hub t' ≤ hub t + clip1 t * (t' - t) + (t' - t) ^ 2 / 2 := by
  have hg : ∀ u, HasGradientAt hub (clip1 u) u := fun u => (hub_hasDerivAt u).hasGradientAt'
  have hl : ∀ u v, ‖clip1 u - clip1 v‖ ≤ 1 * ‖u - v‖ := fun u v => by
    simpa [Real.norm_eq_abs] using clip1_lipschitz u v
  have h := OracleTemplate.Gradient.smooth_upper_bound hg hl t t'
  rw [RCLike.inner_apply, conj_trivial, Real.norm_eq_abs, sq_abs] at h
  linarith

lemma hub_lower (t t' : ℝ) : hub t + clip1 t * (t' - t) - (t' - t) ^ 2 / 2 ≤ hub t' := by
  have hg : ∀ u, HasGradientAt (fun v => -hub v) (-clip1 u) u := fun u =>
    (hub_hasDerivAt u).neg.hasGradientAt'
  have hl : ∀ u v, ‖-clip1 u - -clip1 v‖ ≤ 1 * ‖u - v‖ := fun u v => by
    rw [neg_sub_neg, norm_sub_rev]
    simpa [Real.norm_eq_abs] using clip1_lipschitz u v
  have h := OracleTemplate.Gradient.smooth_upper_bound hg hl t t'
  rw [RCLike.inner_apply, conj_trivial, Real.norm_eq_abs, sq_abs] at h
  linarith

lemma hub_abs_le (t : ℝ) : |hub t| ≤ t ^ 2 / 2 := by
  have h1 := hub_upper 0 t
  have h2 := hub_lower 0 t
  rw [hub_zero, clip1_zero] at h1 h2
  rw [abs_le]
  constructor <;> nlinarith

section tpInstance

variable (q : Params) (hd : 0 < q.d)

noncomputable def L1 : ℝ := q.L / 2

noncomputable def m1 : ℝ := 8 * q.μ / 5

noncomputable def Yv : ℝ := 8 * q.ε / q.L

noncomputable def Wv : ℝ := 2 * Yv q

noncomputable def th : ℝ := 3 * m1 q * Yv q / 4

noncomputable def TT : ℝ := (q.σ / (2 * th q)) ^ rr q

noncomputable def rho : ℝ := 1 / max 1 (2 * TT q)

noncomputable def ev : Sp q := unitVector q.d hd

noncomputable def tpF (s : ℝ) (x y : Sp q) : ℝ :=
  L1 q * ⟪ev q hd, x⟫ * ⟪ev q hd, y⟫ - L1 q * Yv q * ⟪ev q hd, x⟫ - m1 q / 2 * ‖y‖ ^ 2 +
    s * th q * Wv q * hub (⟪ev q hd, y⟫ / Wv q)

noncomputable def tpGx (z : Sp q × Sp q) : Sp q := (L1 q * (⟪ev q hd, z.2⟫ - Yv q)) • ev q hd

noncomputable def tpGy (s : ℝ) (z : Sp q × Sp q) : Sp q :=
  (L1 q * ⟪ev q hd, z.1⟫ + s * th q * clip1 (⟪ev q hd, z.2⟫ / Wv q)) • ev q hd - m1 q • z.2

noncomputable def tpOy (s : ℝ) (z : Sp q × Sp q) (ω : ℝ) : Sp q :=
  (L1 q * ⟪ev q hd, z.1⟫ + reveal (rho q) ω * (s * th q * clip1 (⟪ev q hd, z.2⟫ / Wv q))) •
    ev q hd - m1 q • z.2

noncomputable def tpOracle (s : ℝ) : Oracle (Sp q × Sp q) (Sp q × Sp q) where
  Seed := fun _ => ℝ
  law := ⟨stream, inferInstance⟩
  answer := fun _ (_, z) ω => (tpGx q hd z, tpOy q hd s z ω)

end tpInstance

section tpfacts

variable {q : Params} (hv : spec.valid q) (hd : 0 < q.d)
include hv

lemma L1_pos : 0 < L1 q := by unfold L1; have := L_pos hv; positivity

lemma m1_pos : 0 < m1 q := by unfold m1; have := mu_pos hv; positivity

lemma Yv_pos : 0 < Yv q := by unfold Yv; have := L_pos hv; have := eps_pos hv; positivity

lemma Wv_pos : 0 < Wv q := by unfold Wv; have := Yv_pos hv; positivity

lemma th_pos : 0 < th q := by unfold th; have := m1_pos hv; have := Yv_pos hv; positivity

lemma th_W : th q / Wv q = 3 * m1 q / 8 := by
  unfold th Wv
  have := Yv_pos hv
  field_simp
  ring

lemma m1_sub : m1 q - th q / Wv q = q.μ := by
  rw [th_W hv]; unfold m1; ring

lemma eps_L1 : q.ε / L1 q = Yv q / 4 := by
  unfold L1 Yv
  have := L_pos hv
  field_simp
  ring

omit hv in
lemma rho_pos : 0 < rho q := by
  unfold rho
  exact div_pos one_pos (lt_max_of_lt_left one_pos)

omit hv in
lemma rho_le : rho q ≤ 1 := by
  unfold rho
  rw [div_le_one (lt_max_of_lt_left one_pos)]
  exact le_max_left _ _

lemma TT_nonneg : 0 ≤ TT q := by
  unfold TT
  have := sigma_nonneg hv
  have := th_pos hv
  exact Real.rpow_nonneg (by positivity) _

include hd

omit hv in
lemma ev_norm : ‖ev q hd‖ = 1 := unitVector_norm q.d hd

omit hv in
lemma inner_ev_le (y : Sp q) : |⟪ev q hd, y⟫| ≤ ‖y‖ := by
  have h := abs_real_inner_le_norm (ev q hd) y
  rwa [ev_norm hd, one_mul] at h

omit hv in
lemma tp_grad_x (s : ℝ) (x y : Sp q) :
    HasGradientAt (fun x' => tpF q hd s x' y) (tpGx q hd (x, y)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hi : HasFDerivAt (fun x' : Sp q => ⟪ev q hd, x'⟫) (innerSL ℝ (ev q hd)) x :=
    (innerSL ℝ (ev q hd)).hasFDerivAt
  have h := ((hi.const_mul (L1 q)).mul_const ⟪ev q hd, y⟫).sub (hi.const_mul (L1 q * Yv q))
  have h2 := (h.sub_const (m1 q / 2 * ‖y‖ ^ 2)).add_const
    (s * th q * Wv q * hub (⟪ev q hd, y⟫ / Wv q))
  refine h2.congr_fderiv ?_
  ext v
  simp only [tpGx, InnerProductSpace.toDual_apply_apply, real_inner_smul_left]
  simp [innerSL_apply_apply]
  ring

lemma tp_grad_y (s : ℝ) (x y : Sp q) :
    HasGradientAt (fun y' => tpF q hd s x y') (tpGy q hd s (x, y)) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hi : HasFDerivAt (fun y' : Sp q => ⟪ev q hd, y'⟫) (innerSL ℝ (ev q hd)) y :=
    (innerSL ℝ (ev q hd)).hasFDerivAt
  have hW := Wv_pos hv
  have hh : HasFDerivAt (fun y' : Sp q => hub (⟪ev q hd, y'⟫ / Wv q))
      (clip1 (⟪ev q hd, y⟫ / Wv q) • ((1 / Wv q) • innerSL ℝ (ev q hd))) y := by
    have hlin : HasFDerivAt (fun y' : Sp q => ⟪ev q hd, y'⟫ / Wv q)
        ((1 / Wv q) • innerSL ℝ (ev q hd)) y :=
      (hi.const_mul (1 / Wv q)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => by ring)
    exact (hub_hasDerivAt (⟪ev q hd, y⟫ / Wv q)).comp_hasFDerivAt y hlin
  have hn := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul (m1 q / 2)
  have h := (((hi.const_mul (L1 q * ⟪ev q hd, x⟫)).sub_const (L1 q * Yv q * ⟪ev q hd, x⟫)).sub hn).add
    (hh.const_mul (s * th q * Wv q))
  refine h.congr_fderiv ?_
  ext v
  simp only [tpGy, InnerProductSpace.toDual_apply_apply, inner_sub_left, real_inner_smul_left]
  simp [innerSL_apply_apply, real_inner_comm]
  field_simp
  ring

lemma tp_smooth (s : ℝ) (hs : s * s = 1) (z z' : Sp q × Sp q) :
    ‖tpGx q hd z - tpGx q hd z'‖ ^ 2 + ‖tpGy q hd s z - tpGy q hd s z'‖ ^ 2 ≤
      q.L ^ 2 * (‖z.1 - z'.1‖ ^ 2 + ‖z.2 - z'.2‖ ^ 2) := by
  have he := ev_norm hd
  have hL1 := L1_pos hv
  have hth := th_pos hv
  have hW := Wv_pos hv
  have hm := m1_pos hv
  have hsa : |s| = 1 := by
    have : |s| * |s| = 1 := by rw [← abs_mul, hs, abs_one]
    nlinarith [abs_nonneg s]
  set dx := z.1 - z'.1
  set dy := z.2 - z'.2
  have hax : |⟪ev q hd, z.1⟫ - ⟪ev q hd, z'.1⟫| ≤ ‖dx‖ := by
    rw [← inner_sub_right]; exact inner_ev_le hd _
  have hay : |⟪ev q hd, z.2⟫ - ⟪ev q hd, z'.2⟫| ≤ ‖dy‖ := by
    rw [← inner_sub_right]; exact inner_ev_le hd _
  have hgx : ‖tpGx q hd z - tpGx q hd z'‖ ≤ L1 q * ‖dy‖ := by
    simp only [tpGx, ← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs]
    rw [show L1 q * (⟪ev q hd, z.2⟫ - Yv q) - L1 q * (⟪ev q hd, z'.2⟫ - Yv q) =
      L1 q * (⟪ev q hd, z.2⟫ - ⟪ev q hd, z'.2⟫) by ring, abs_mul, abs_of_pos hL1]
    exact mul_le_mul_of_nonneg_left hay hL1.le
  have hclip : |clip1 (⟪ev q hd, z.2⟫ / Wv q) - clip1 (⟪ev q hd, z'.2⟫ / Wv q)| ≤ ‖dy‖ / Wv q := by
    refine (clip1_lipschitz _ _).trans ?_
    rw [← sub_div, abs_div, abs_of_pos hW]
    exact div_le_div_of_nonneg_right hay hW.le
  have hgy : ‖tpGy q hd s z - tpGy q hd s z'‖ ≤ L1 q * ‖dx‖ + (th q / Wv q + m1 q) * ‖dy‖ := by
    have heq : tpGy q hd s z - tpGy q hd s z' =
        (L1 q * (⟪ev q hd, z.1⟫ - ⟪ev q hd, z'.1⟫) +
          s * th q * (clip1 (⟪ev q hd, z.2⟫ / Wv q) - clip1 (⟪ev q hd, z'.2⟫ / Wv q))) • ev q hd -
          m1 q • dy := by
      simp only [tpGy, dy, smul_sub, sub_smul, add_smul, mul_sub]
      abel
    rw [heq]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, he, mul_one, Real.norm_eq_abs, Real.norm_of_nonneg hm.le]
    have h1 : |L1 q * (⟪ev q hd, z.1⟫ - ⟪ev q hd, z'.1⟫) +
        s * th q * (clip1 (⟪ev q hd, z.2⟫ / Wv q) - clip1 (⟪ev q hd, z'.2⟫ / Wv q))| ≤
        L1 q * ‖dx‖ + th q * (‖dy‖ / Wv q) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_mul, hsa, one_mul, abs_of_pos hL1, abs_of_pos hth]
      gcongr
    have h2 : th q * (‖dy‖ / Wv q) = th q / Wv q * ‖dy‖ := by ring
    nlinarith
  have hc : th q / Wv q + m1 q = 11 / 5 * q.μ := by rw [th_W hv]; unfold m1; ring
  rw [hc] at hgy
  have hμ := mu_pos hv
  have h8 : 8 * q.μ ≤ q.L := hv.2.2.1
  have hL1v : L1 q = q.L / 2 := rfl
  have e1 := pow_le_pow_left₀ (norm_nonneg _) hgx 2
  have e2 := pow_le_pow_left₀ (norm_nonneg _) hgy 2
  have e3 := LongTails.Proofs.HeavyTailNcscLift.inner_bound_sq (L1 q) (11 / 5 * q.μ) ‖dx‖ ‖dy‖
  rw [hL1v] at e1 e2 e3
  have hdx := sq_nonneg ‖dx‖
  have hdy := sq_nonneg ‖dy‖
  have hμL : 64 * q.μ ^ 2 ≤ q.L ^ 2 := by nlinarith
  have key := mul_le_mul_of_nonneg_right hμL (add_nonneg hdx hdy)
  nlinarith [key, e1, e2, e3, mul_nonneg (sq_nonneg q.L) hdx, mul_nonneg (sq_nonneg q.L) hdy]

omit hv hd in
lemma hub_dev (s : ℝ) (hs : s * s = 1) (t t' : ℝ) :
    s * hub t' ≤ s * hub t + s * clip1 t * (t' - t) + (t' - t) ^ 2 / 2 := by
  have h1 := hub_upper t t'
  have h2 := hub_lower t t'
  rcases mul_self_eq_one_iff.mp hs with rfl | rfl <;> nlinarith

lemma tp_concave (s : ℝ) (hs : s * s = 1) (x y y' : Sp q) :
    tpF q hd s x y' ≤ tpF q hd s x y + ⟪tpGy q hd s (x, y), y' - y⟫ - q.μ / 2 * ‖y' - y‖ ^ 2 := by
  have hW := Wv_pos hv
  have hth := th_pos hv
  have hdev := hub_dev s hs (⟪ev q hd, y⟫ / Wv q) (⟪ev q hd, y'⟫ / Wv q)
  have hm := mul_le_mul_of_nonneg_left hdev (show 0 ≤ th q * Wv q by positivity)
  have hb : (⟪ev q hd, y'⟫ - ⟪ev q hd, y⟫) ^ 2 ≤ ‖y' - y‖ ^ 2 := by
    rw [← inner_sub_right]
    have := inner_ev_le hd (y' - y)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hsq : ‖y'‖ ^ 2 = ‖y‖ ^ 2 + 2 * ⟪y, y' - y⟫ + ‖y' - y‖ ^ 2 := by
    have he : y' = y + (y' - y) := by abel
    conv_lhs => rw [he]
    rw [norm_add_sq_real]
  have hgy : ⟪tpGy q hd s (x, y), y' - y⟫ =
      (L1 q * ⟪ev q hd, x⟫ + s * th q * clip1 (⟪ev q hd, y⟫ / Wv q)) *
        (⟪ev q hd, y'⟫ - ⟪ev q hd, y⟫) - m1 q * ⟪y, y' - y⟫ := by
    simp only [tpGy, inner_sub_left, real_inner_smul_left, inner_sub_right]
    ring
  have hdiv : (⟪ev q hd, y'⟫ / Wv q - ⟪ev q hd, y⟫ / Wv q) =
      (⟪ev q hd, y'⟫ - ⟪ev q hd, y⟫) / Wv q := by ring
  rw [hdiv] at hm
  have hkey : th q * Wv q * (((⟪ev q hd, y'⟫ - ⟪ev q hd, y⟫) / Wv q) ^ 2 / 2) =
      th q / Wv q / 2 * (⟪ev q hd, y'⟫ - ⟪ev q hd, y⟫) ^ 2 := by field_simp
  have hkey2 : th q * Wv q * (s * clip1 (⟪ev q hd, y⟫ / Wv q) *
      ((⟪ev q hd, y'⟫ - ⟪ev q hd, y⟫) / Wv q)) =
      s * th q * clip1 (⟪ev q hd, y⟫ / Wv q) * (⟪ev q hd, y'⟫ - ⟪ev q hd, y⟫) := by field_simp
  have hμ := m1_sub hv
  have hthW : 0 ≤ th q / Wv q := by positivity
  simp only [tpF]
  rw [hgy, hsq]
  nlinarith [mul_le_mul_of_nonneg_left hb hthW]

lemma tp_gap (s : ℝ) (hs : s * s = 1) (x y : Sp q) :
    tpF q hd s 0 y - tpF q hd s x (Yv q • ev q hd) ≤ q.Δ := by
  have hW := Wv_pos hv
  have hth := th_pos hv
  have hm1 := m1_pos hv
  have hY := Yv_pos hv
  have he := ev_norm hd
  have hsa : |s| = 1 := by
    have : |s| * |s| = 1 := by rw [← abs_mul, hs, abs_one]
    nlinarith [abs_nonneg s]
  have h1 : tpF q hd s 0 y ≤ 0 := by
    have hh := hub_abs_le (⟪ev q hd, y⟫ / Wv q)
    have hb : ⟪ev q hd, y⟫ ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (inner_ev_le hd y) 2
    have hsh : s * th q * Wv q * hub (⟪ev q hd, y⟫ / Wv q) ≤
        th q * Wv q * ((⟪ev q hd, y⟫ / Wv q) ^ 2 / 2) := by
      have : s * th q * Wv q * hub (⟪ev q hd, y⟫ / Wv q) ≤
          |s * th q * Wv q * hub (⟪ev q hd, y⟫ / Wv q)| := le_abs_self _
      rw [abs_mul, abs_mul, abs_mul, hsa, abs_of_pos hth, abs_of_pos hW, one_mul] at this
      nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ th q * Wv q by positivity)]
    have hk : th q * Wv q * ((⟪ev q hd, y⟫ / Wv q) ^ 2 / 2) = th q / Wv q / 2 * ⟪ev q hd, y⟫ ^ 2 := by
      field_simp
    have hμ := m1_sub hv
    have hμ0 := mu_pos hv
    simp only [tpF, inner_zero_right, mul_zero, zero_mul, sub_zero, zero_sub]
    nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ th q / Wv q by positivity)]
  have h2 : -(11 / 16 * m1 q * Yv q ^ 2) ≤ tpF q hd s x (Yv q • ev q hd) := by
    have hi : ⟪ev q hd, Yv q • ev q hd⟫ = Yv q := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq, he]; ring
    have hn : ‖Yv q • ev q hd‖ ^ 2 = Yv q ^ 2 := by
      rw [norm_smul, he, mul_one, Real.norm_of_nonneg hY.le]
    have hh := hub_abs_le (Yv q / Wv q)
    have hYW : Yv q / Wv q = 1 / 2 := by unfold Wv; field_simp
    rw [hYW] at hh
    have hsh : -(th q * Wv q * ((1 / 2 : ℝ) ^ 2 / 2)) ≤ s * th q * Wv q * hub (1 / 2) := by
      have : -|s * th q * Wv q * hub (1 / 2)| ≤ s * th q * Wv q * hub (1 / 2) := neg_abs_le _
      rw [abs_mul, abs_mul, abs_mul, hsa, abs_of_pos hth, abs_of_pos hW, one_mul] at this
      nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ th q * Wv q by positivity)]
    have hW2 : Wv q = 2 * Yv q := rfl
    have hth2 : th q = 3 * m1 q * Yv q / 4 := rfl
    simp only [tpF, hi, hn, hYW]
    rw [hW2, hth2] at hsh
    rw [hW2, hth2]
    nlinarith
  have h3 : 11 / 16 * m1 q * Yv q ^ 2 ≤ q.Δ := by
    have hreg : 2 ^ 32 * q.ε ^ 2 ≤ q.L * q.Δ := hv.2.2.2.1
    have hL := L_pos hv
    have hμ := mu_pos hv
    have h8 : 8 * q.μ ≤ q.L := hv.2.2.1
    have hval : 11 / 16 * m1 q * Yv q ^ 2 = 352 / 5 * q.μ * q.ε ^ 2 / q.L ^ 2 := by
      unfold m1 Yv; field_simp; ring
    rw [hval, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg q.ε, mul_le_mul_of_nonneg_left h8 (sq_nonneg q.ε)]
  linarith

end tpfacts


section tpadm

variable {q : Params} (hv : spec.valid q) (hd : 0 < q.d)
include hv hd

omit hv in
lemma tp_oy_sub (s : ℝ) (z : Sp q × Sp q) (ω : ℝ) :
    tpOy q hd s z ω - tpGy q hd s z =
      ((reveal (rho q) ω - 1) * (s * th q * clip1 (⟪ev q hd, z.2⟫ / Wv q))) • ev q hd := by
  simp only [tpOy, tpGy, sub_mul, one_mul, add_smul, sub_smul]
  abel

lemma tp_moment_eq (s : ℝ) (hs : s * s = 1) (z : Sp q × Sp q) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ th q ∧
      (fun ω => (Real.sqrt (‖tpGx q hd z - tpGx q hd z‖ ^ 2 + ‖tpOy q hd s z ω - tpGy q hd s z‖ ^ 2)) ^ q.p) =
        fun ω => if ω ≤ rho q then ((1 / rho q - 1) * a) ^ q.p else a ^ q.p := by
  have hsa : |s| = 1 := by
    have : |s| * |s| = 1 := by rw [← abs_mul, hs, abs_one]
    nlinarith [abs_nonneg s]
  have hth := th_pos hv
  set a := |s * th q * clip1 (⟪ev q hd, z.2⟫ / Wv q)|
  have ha : a ≤ th q := by
    simp only [a, abs_mul, hsa, one_mul, abs_of_pos hth]
    have := clip1_abs (⟪ev q hd, z.2⟫ / Wv q)
    nlinarith
  refine ⟨a, abs_nonneg _, ha, ?_⟩
  funext ω
  rw [sub_self, norm_zero, tp_oy_sub hd s z ω, norm_smul, ev_norm hd, mul_one,
    Real.norm_eq_abs, abs_mul]
  have hsq : Real.sqrt ((0 : ℝ) ^ 2 + (|reveal (rho q) ω - 1| * a) ^ 2) =
      |reveal (rho q) ω - 1| * a := by
    rw [zero_pow two_ne_zero, zero_add, Real.sqrt_sq (by positivity)]
  rw [hsq]
  have hr0 := rho_pos (q := q)
  have hr1 := rho_le (q := q)
  unfold reveal
  split_ifs with h
  · rw [abs_of_nonneg (by rw [sub_nonneg, le_div_iff₀ hr0]; linarith)]
  · norm_num

omit hd in
lemma tp_moment_bound {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ th q) :
    rho q * ((1 / rho q - 1) * a) ^ q.p + (1 - rho q) * a ^ q.p ≤ q.σ ^ q.p := by
  have hp1 : 1 < q.p := hv.1.2.2.1
  have hσ := sigma_nonneg hv
  have hth := th_pos hv
  have hT := TT_nonneg hv
  have hr0 := rho_pos (q := q)
  have hr1 := rho_le (q := q)
  rcases le_or_gt (2 * TT q) 1 with hC | hC
  · have h1 : rho q = 1 := by unfold rho; rw [max_eq_left hC, div_one]
    rw [h1]
    simp only [div_one, sub_self, zero_mul, one_mul, add_zero]
    rw [Real.zero_rpow (by linarith)]
    exact Real.rpow_nonneg hσ _
  · have ht : rho q = (2 * TT q)⁻¹ := by unfold rho; rw [max_eq_right hC.le, one_div]
    refine (moment_scalar hr0 hr1 ha0 hp1.le).trans ?_
    have hTp : 0 < TT q := by linarith
    have hpow : rho q ^ (1 - q.p) = 2 ^ (q.p - 1) * (q.σ / (2 * th q)) ^ q.p := by
      rw [ht, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_sub,
        Real.mul_rpow (by norm_num) hT, TT, ← Real.rpow_mul (by positivity), rr_mul hv]
    have hap : a ^ q.p ≤ th q ^ q.p := Real.rpow_le_rpow ha0 ha (by linarith)
    have h2 : (2 : ℝ) * 2 ^ (q.p - 1) = 2 ^ q.p := by
      rw [← Real.rpow_one_add' (by norm_num) (by linarith)]
      ring_nf
    have hval : 2 * (q.σ / (2 * th q)) * th q = q.σ := by field_simp
    calc 2 * rho q ^ (1 - q.p) * a ^ q.p ≤ 2 * rho q ^ (1 - q.p) * th q ^ q.p := by gcongr
      _ = (2 * (q.σ / (2 * th q)) * th q) ^ q.p := by
          rw [hpow, Real.mul_rpow (by positivity) hth.le, Real.mul_rpow (by norm_num) (by positivity),
            ← h2]
          ring
      _ = q.σ ^ q.p := by rw [hval]

omit hv in
lemma tp_ox_integrable (z : Sp q × Sp q) :
    Integrable (fun _ : ℝ => tpGx q hd z) unif := integrable_const _

omit hv in
lemma tp_ox_mean (z : Sp q × Sp q) : ∫ _ω, tpGx q hd z ∂unif = tpGx q hd z := by simp

omit hv in
lemma tp_oy_integrable (s : ℝ) (z : Sp q × Sp q) : Integrable (tpOy q hd s z) unif :=
  (((integrable_const _).add ((reveal_integrable (rho_pos (q := q))).mul_const _)).smul_const _).sub
    (integrable_const _)

omit hv in
lemma tp_oy_mean (s : ℝ) (z : Sp q × Sp q) : ∫ ω, tpOy q hd s z ω ∂unif = tpGy q hd s z := by
  have hr0 := rho_pos (q := q)
  have hr1 := rho_le (q := q)
  have hi1 : Integrable (fun ω => L1 q * ⟪ev q hd, z.1⟫ +
      reveal (rho q) ω * (s * th q * clip1 (⟪ev q hd, z.2⟫ / Wv q))) unif :=
    (integrable_const _).add ((reveal_integrable hr0).mul_const _)
  have hint : ∫ ω, (L1 q * ⟪ev q hd, z.1⟫ +
      reveal (rho q) ω * (s * th q * clip1 (⟪ev q hd, z.2⟫ / Wv q))) ∂unif =
      L1 q * ⟪ev q hd, z.1⟫ + s * th q * clip1 (⟪ev q hd, z.2⟫ / Wv q) := by
    rw [integral_add (integrable_const _) ((reveal_integrable hr0).mul_const _), integral_const,
      probReal_univ, one_smul, integral_mul_const, reveal_integral hr0 hr1, one_mul]
  unfold tpOy tpGy
  rw [integral_sub (f := fun ω => (L1 q * ⟪ev q hd, z.1⟫ +
      reveal (rho q) ω * (s * th q * clip1 (⟪ev q hd, z.2⟫ / Wv q))) • ev q hd)
    (g := fun _ => m1 q • z.2) (hi1.smul_const _) (integrable_const _), integral_smul_const, hint,
    integral_const, probReal_univ, one_smul]

lemma tp_moment_integrable (s : ℝ) (hs : s * s = 1) (z : Sp q × Sp q) :
    Integrable (fun ω => (Real.sqrt (‖tpGx q hd z - tpGx q hd z‖ ^ 2 +
      ‖tpOy q hd s z ω - tpGy q hd s z‖ ^ 2)) ^ q.p) unif := by
  obtain ⟨a, _, _, he'⟩ := tp_moment_eq hv hd s hs z
  rw [he']
  exact (two_value_integral (rho_pos (q := q)).le (rho_le (q := q)) (((1 / rho q - 1) * a) ^ q.p)
    (a ^ q.p)).1

lemma tp_moment_le (s : ℝ) (hs : s * s = 1) (z : Sp q × Sp q) :
    ∫ ω, (Real.sqrt (‖tpGx q hd z - tpGx q hd z‖ ^ 2 +
      ‖tpOy q hd s z ω - tpGy q hd s z‖ ^ 2)) ^ q.p ∂unif ≤ q.σ ^ q.p := by
  obtain ⟨a, ha0, ha, he'⟩ := tp_moment_eq hv hd s hs z
  rw [he', (two_value_integral (rho_pos (q := q)).le (rho_le (q := q)) _ _).2]
  exact tp_moment_bound hv ha0 ha

lemma tp_admissible (s : ℝ) (hs : s * s = 1) :
    spec.admissible q (tpF q hd s) (tpOracle q hd s) := by
  have hr0 := rho_pos (q := q)
  have hr1 := rho_le (q := q)
  have he := ev_norm hd
  refine ⟨tpGx q hd, tpGy q hd s, fun z _ => tpGx q hd z, tpOy q hd s,
    ⟨unif, inferInstanceAs (IsProbabilityMeasure unif)⟩,
    ⟨stream, inferInstanceAs (IsProbabilityMeasure stream)⟩, stream_iid, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact tp_grad_x hd s
  · exact tp_grad_y hv hd s
  · exact tp_smooth hv hd s hs
  · exact tp_concave hv hd s hs
  · intro x y
    exact ⟨Yv q • ev q hd, tp_gap hv hd s hs x y⟩
  · change ‖tpGy q hd s (0, 0)‖ ≤ q.G
    have hG : 0 ≤ q.G := hv.1.2.2.2.2.2.2.1
    simp [tpGy, clip1_zero, hG]
  · exact (by unfold tpGx; fun_prop : Continuous fun z : Sp q × Sp q => tpGx q hd z).measurable.comp
      measurable_fst
  · have hc1 : Continuous fun z : Sp q × Sp q => L1 q * ⟪ev q hd, z.1⟫ := by fun_prop
    have hc2 : Continuous fun z : Sp q × Sp q => s * th q * clip1 (⟪ev q hd, z.2⟫ / Wv q) := by
      have := clip1_continuous
      fun_prop
    have hc3 : Continuous fun z : Sp q × Sp q => m1 q • z.2 := by fun_prop
    have hr : Measurable fun zw : (Sp q × Sp q) × ℝ => reveal (rho q) zw.2 :=
      (measurable_reveal _).comp measurable_snd
    exact (((hc1.measurable.comp measurable_fst).add (hr.mul (hc2.measurable.comp measurable_fst))).smul_const
      (ev q hd)).sub (hc3.measurable.comp measurable_fst)
  · exact fun z => tp_ox_integrable hd z
  · exact fun z => tp_oy_integrable hd s z
  · exact fun z => tp_ox_mean hd z
  · exact fun z => tp_oy_mean hd s z
  · exact fun z => tp_moment_integrable hv hd s hs z
  · exact fun z => tp_moment_le hv hd s hs z

lemma tp_phi_gradient (s : ℝ) (hs : s * s = 1) (ys : Sp q → Sp q)
    (hys : ∀ x y, tpF q hd s x y ≤ tpF q hd s x (ys x)) (x : Sp q) :
    gradient (fun x => tpF q hd s x (ys x)) x = tpGx q hd (x, ys x) ∧ tpGy q hd s (x, ys x) = 0 := by
  have Hm := LongTails.Proofs.HeavyTailSaddleGeometry.minimax_value_hyp (E := Sp q) (F := Sp q)
    (mu_pos hv) hv.1.2.1 (tp_grad_x hd s) (tp_grad_y hv hd s) (tp_smooth hv hd s hs)
    (tp_concave hv hd s hs)
  have hmax : (fun x => tpF q hd s x (ys x)) = LongTails.Setups.StochasticTwoSidedPL.maxValue
      (tpF q hd s) := funext fun x => (Hm.max_value_eq (hys x)).symm
  rw [hmax]
  exact ⟨(Hm.value_hasGradient (hys x)).gradient, Hm.max_gradient_zero (hys x)⟩

lemma tp_not_both (x yp ym : Sp q) (hp0 : tpGy q hd 1 (x, yp) = 0) (hm0 : tpGy q hd (-1) (x, ym) = 0)
    (hpg : ‖tpGx q hd (x, yp)‖ ≤ q.ε) (hmg : ‖tpGx q hd (x, ym)‖ ≤ q.ε) : False := by
  have he := ev_norm hd
  have hL1 := L1_pos hv
  have hm1 := m1_pos hv
  have hY := Yv_pos hv
  have hW := Wv_pos hv
  have hee : ⟪ev q hd, ev q hd⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have heq (s : ℝ) (y : Sp q) (h0 : tpGy q hd s (x, y) = 0) :
      L1 q * ⟪ev q hd, x⟫ + s * th q * clip1 (⟪ev q hd, y⟫ / Wv q) = m1 q * ⟪ev q hd, y⟫ := by
    have h := congrArg (fun v => ⟪ev q hd, v⟫) h0
    simp only [tpGy, inner_sub_right, real_inner_smul_right, hee, inner_zero_right] at h
    linarith
  have hnorm (y : Sp q) (h : ‖tpGx q hd (x, y)‖ ≤ q.ε) : |⟪ev q hd, y⟫ - Yv q| ≤ Yv q / 4 := by
    simp only [tpGx, norm_smul, he, mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos hL1] at h
    rw [← eps_L1 hv, le_div_iff₀ hL1]
    linarith
  have hclip (y : Sp q) (h : |⟪ev q hd, y⟫ - Yv q| ≤ Yv q / 4) :
      clip1 (⟪ev q hd, y⟫ / Wv q) = ⟪ev q hd, y⟫ / Wv q := by
    rw [abs_le] at h
    apply clip1_of_mem
    · rw [le_div_iff₀ hW]; unfold Wv; linarith
    · rw [div_le_iff₀ hW]; unfold Wv; linarith
  have h1 := heq 1 yp hp0
  have h2 := heq (-1) ym hm0
  have b1 := hnorm yp hpg
  have b2 := hnorm ym hmg
  rw [hclip yp b1] at h1
  rw [hclip ym b2] at h2
  rw [abs_le] at b1 b2
  have hth : th q = 3 * m1 q * Wv q / 8 := by unfold th Wv; ring
  rw [hth] at h1 h2
  field_simp at h1 h2
  nlinarith [mul_pos hm1 hY, mul_le_mul_of_nonneg_left b1.2 hm1.le,
    mul_le_mul_of_nonneg_left b2.1 hm1.le]

lemma tp_failure (A : Algorithm (Sp q × Sp q) (Sp q × Sp q) (Sp q)) (N : ℕ)
    (hN : (N : ℝ) ≤ TT q / 2) :
    ∃ s : ℝ, s * s = 1 ∧
      ¬ spec.successful q (tpF q hd s)
        (fun w : A.Seed × ((k : ℕ) → (tpOracle q hd s).Seed k) =>
          execute (tpOracle q hd s) A (fun _ => N) w.1 w.2)
        ⟨(A.law : Measure _).prod ((tpOracle q hd s).law : Measure _), inferInstance⟩ := by
  have hr0 := rho_pos (q := q)
  have hr1 := rho_le (q := q)
  have hδ : q.δ ≤ 1 / 4 := hv.2.1
  by_contra hcon
  push Not at hcon
  let P : Measure (A.Seed × (ℕ → ℝ)) := (A.law : Measure A.Seed).prod stream
  let out : ℝ → A.Seed × (ℕ → ℝ) → Sp q := fun s w => execute (tpOracle q hd s) A (fun _ => N) w.1 w.2
  obtain ⟨_, ⟨yp, hyp⟩, hbp⟩ := hcon 1 (by norm_num)
  obtain ⟨_, ⟨ym, hym⟩, hbm⟩ := hcon (-1) (by norm_num)
  let bad : ℝ → (Sp q → Sp q) → Set (A.Seed × (ℕ → ℝ)) := fun s ys =>
    {w | q.ε < ‖gradient (fun x => tpF q hd s x (ys x)) (out s w)‖}
  have hreal (s : ℝ) (ys : Sp q → Sp q) (h : (P : Measure _) (bad s ys) ≤ ENNReal.ofReal q.δ) :
      P.real (bad s ys) ≤ q.δ := by
    have hδ0 : 0 ≤ q.δ := hv.1.2.2.2.2.2.2.2.2.1.le
    have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_ofReal hδ0] at h'
  have hp := hreal 1 yp (hbp yp hyp)
  have hm := hreal (-1) ym (hbm ym hym)
  let Ev : Set (ℕ → ℝ) := {ω | ∀ k ∈ Finset.range N, ω k ∈ Set.Ioi (rho q)}
  have hEv : MeasurableSet Ev := measurableSet_no_reveal _ N
  have hsub : (Prod.snd ⁻¹' Ev : Set (A.Seed × (ℕ → ℝ))) ⊆ bad 1 yp ∪ bad (-1) ym := by
    intro w hw
    have hsame : out 1 w = out (-1) w := by
      apply execute_congr (tpOracle q hd 1) (tpOracle q hd (-1)) A N w.1 w.2 w.2
        (fun k z => (tpGx q hd z.2, tpOy q hd 1 z.2 (w.2 k)))
        (fun k z => (tpGx q hd z.2, tpOy q hd (-1) z.2 (w.2 k)))
        (fun _ _ => rfl) (fun _ _ => rfl)
      intro k hk z
      have hk' : rho q < w.2 k := hw k (Finset.mem_range.mpr hk)
      have hr : reveal (rho q) (w.2 k) = 0 := by simp [reveal, not_le.mpr hk']
      simp only [tpOy, hr, zero_mul, add_zero]
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    obtain ⟨g1, g2⟩ := hnot
    simp only [bad, Set.mem_ofPred_eq, not_lt] at g1 g2
    have e1 := tp_phi_gradient hv hd 1 (by norm_num) yp hyp (out 1 w)
    have e2 := tp_phi_gradient hv hd (-1) (by norm_num) ym hym (out (-1) w)
    rw [e1.1] at g1
    rw [e2.1, ← hsame] at g2
    rw [← hsame] at e2
    exact tp_not_both hv hd (out 1 w) (yp (out 1 w)) (ym (out 1 w)) e1.2 e2.2 g1 g2
  have hPE : P.real (Prod.snd ⁻¹' Ev) = (1 - rho q) ^ N := by
    have hmap : P.map Prod.snd = stream := by
      dsimp only [P]; rw [Measure.map_snd_prod]; simp
    rw [Measure.real, ← Measure.map_apply measurable_snd hEv, hmap]
    exact stream_no_reveal hr0.le hr1 N
  have hNr : (N : ℝ) * rho q ≤ 1 / 4 := by
    have hT := TT_nonneg hv
    have hmx : 0 < max 1 (2 * TT q) := lt_max_of_lt_left one_pos
    unfold rho
    rw [mul_one_div, div_le_iff₀ hmx]
    have : TT q / 2 ≤ max 1 (2 * TT q) / 4 := by
      have := le_max_right 1 (2 * TT q)
      linarith
    nlinarith
  have hbern : 1 - (N : ℝ) * rho q ≤ (1 - rho q) ^ N := by
    have h := one_add_mul_le_pow (a := -rho q) (by linarith) N
    simpa [sub_eq_add_neg, mul_neg] using h
  have hle : P.real (Prod.snd ⁻¹' Ev) ≤ 2 * q.δ :=
    calc P.real (Prod.snd ⁻¹' Ev) ≤ P.real (bad 1 yp ∪ bad (-1) ym) := measureReal_mono hsub
      _ ≤ P.real (bad 1 yp) + P.real (bad (-1) ym) := measureReal_union_le _ _
      _ ≤ 2 * q.δ := by linarith
  rw [hPE] at hle
  linarith

end tpadm

end LongTails.Proofs.HeavyTailNcscTwoPoint
