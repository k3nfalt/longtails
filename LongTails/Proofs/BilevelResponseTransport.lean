import LongTails.Proofs.BilevelResponseBounds
import LongTails.Proofs.BilevelTransport

set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.BilevelResponseTransport

open LongTails.Setups.HigherSmoothBilevel BilevelGeometry BilevelCurvature BilevelImplicitEstimates
open scoped RealInnerProductSpace

noncomputable def graph {p : Params} (I : Instance p) (x : p.X) : p.X × p.Y :=
  (x, lowerSolution I x)

noncomputable def lift {p : Params} (I : Instance p) (x a : p.X) : p.X × p.Y :=
  (a, fderiv ℝ (lowerSolution I) x a)

noncomputable def second {p : Params} (I : Instance p) (x : p.X) : p.X →L[ℝ] p.X →L[ℝ] p.Y :=
  fderiv ℝ (fderiv ℝ (lowerSolution I)) x

noncomputable def hessian {p : Params} (I : Instance p) (x : p.X) : p.Y →L[ℝ] p.Y :=
  p.L⁻¹ • lowerHessian I (graph I x)

noncomputable def third {p : Params} (I : Instance p) (x : p.X) :
    (p.X × p.Y) →L[ℝ] (p.X × p.Y) →L[ℝ] p.Y :=
  p.L⁻¹ • fderiv ℝ (fderiv ℝ (lowerGradient I)) (graph I x)

lemma normalized_root_identity {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x a b : p.X) :
    hessian I x (second I x b a) = -third I x (lift I x b) (lift I x a) := by
  have hh := BilevelImplicit.root_second_equation (lowerGradient_contDiff hg)
    (lowerSolution_contDiff hg hμ hsc)
    (lowerGradient_root (hg.differentiable (by norm_num)) hμ hsc) x a b
  have he : lowerHessian I (graph I x) (second I x b a) =
      -fderiv ℝ (fderiv ℝ (lowerGradient I)) (graph I x) (lift I x b) (lift I x a) := by
    rw [lowerHessian_eq hg]
    exact eq_neg_of_add_eq_zero_left (by simpa [graph, second, lift, add_comm] using hh)
  simp only [hessian, third, smul_apply, he, smul_neg]

lemma second_continuous {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) : Continuous (second I) := by
  have hs1 : ContDiff ℝ 1 (fderiv ℝ (lowerSolution I)) :=
    (contDiff_succ_iff_fderiv.mp (lowerSolution_contDiff hg hμ hsc)).2.2
  exact (contDiff_succ_iff_fderiv (n := 0)).mp hs1 |>.2.2.continuous

lemma graph_hasFDerivAt {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x : p.X) :
    HasFDerivAt (graph I) ((ContinuousLinearMap.id ℝ p.X).prod (fderiv ℝ (lowerSolution I) x)) x :=
  (hasFDerivAt_id x).prodMk
    ((lowerSolution_contDiff hg hμ hsc).differentiable (by norm_num) x).hasFDerivAt

lemma graph_lipschitz {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hμL : p.μ ≤ p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hLip : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (x y : p.X) : ‖graph I x - graph I y‖ ≤ (p.L / p.μ) * ‖x - y‖ := by
  have hκ : 1 ≤ p.L / p.μ := (le_div_iff₀ hμ).mpr (by simpa using hμL)
  change max ‖x - y‖ ‖lowerSolution I x - lowerSolution I y‖ ≤ _
  exact max_le (by simpa using mul_le_mul_of_nonneg_right hκ (norm_nonneg (x - y)))
    (lowerSolution_lipschitz hg hμ (hμ.le.trans hμL) hsc hLip x y)

lemma lift_norm_bound {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hμL : p.μ ≤ p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hLip : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (x a : p.X) : ‖lift I x a‖ ≤ (p.L / p.μ) * ‖a‖ := by
  have hκ : 1 ≤ p.L / p.μ := (le_div_iff₀ hμ).mpr (by simpa using hμL)
  change max ‖a‖ ‖fderiv ℝ (lowerSolution I) x a‖ ≤ _
  refine max_le (by simpa using mul_le_mul_of_nonneg_right hκ (norm_nonneg a)) ?_
  have hh := (lowerSolution_derivative_bounds hg hμ (hμ.le.trans hμL) hsc hLip x a).1
  calc
    _ ≤ (p.L * ‖a‖) / p.μ := (le_div_iff₀ hμ).mpr (by nlinarith)
    _ = _ := by ring

lemma third_lipschitz {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hL : 0 < p.L)
    (hLip : ∀ z w, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z -
      fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) w‖ ≤ p.L * ‖z - w‖)
    (x y : p.X) : ‖third I x - third I y‖ ≤ ‖graph I x - graph I y‖ := by
  rw [third, third, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hL)]
  calc
    _ ≤ p.L⁻¹ * (p.L * ‖graph I x - graph I y‖) :=
      mul_le_mul_of_nonneg_left (lowerGradient_second_lipschitz hg hLip _ _) (by positivity)
    _ = _ := by field_simp

lemma lift_hasFDerivAt {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x a : p.X) :
    HasFDerivAt (fun y => lift I y a)
      ((0 : p.X →L[ℝ] p.X).prod ((second I x).flip a)) x := by
  have hs1 : ContDiff ℝ 1 (fderiv ℝ (lowerSolution I)) :=
    (contDiff_succ_iff_fderiv.mp (lowerSolution_contDiff hg hμ hsc)).2.2
  have hd := (hs1.differentiable (by norm_num) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const a x)
  have he : HasFDerivAt (fun y => fderiv ℝ (lowerSolution I) y a)
      ((second I x).flip a) x := by
    simpa [second] using hd
  exact (hasFDerivAt_const a x).prodMk he

lemma hessian_hasFDerivAt {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x : p.X) :
    HasFDerivAt (hessian I)
      (p.L⁻¹ • (fderiv ℝ (lowerHessian I) (graph I x)).comp
        ((ContinuousLinearMap.id ℝ p.X).prod (fderiv ℝ (lowerSolution I) x))) x := by
  rw [(lowerHessian_hasFDerivAt hg (graph I x)).fderiv]
  exact ((lowerHessian_hasFDerivAt hg (graph I x)).comp x
    (graph_hasFDerivAt hg hμ hsc x)).const_smul p.L⁻¹

lemma hessian_derivative_apply {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x a : p.X) (v : p.Y) :
    fderiv ℝ (hessian I) x a v = third I x (lift I x a) (0, v) := by
  rw [(hessian_hasFDerivAt hg hμ hsc x).fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply]
  rw [lowerHessian_derivative_apply hg]
  rfl

lemma hessian_coercive {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hL : 0 < p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x : p.X) (v : p.Y) :
    (p.μ / p.L) * ‖v‖ ^ 2 ≤ ⟪hessian I x v, v⟫ := by
  have hc : p.μ * ‖v‖ ^ 2 ≤ ⟪lowerHessian I (graph I x) v, v⟫ := by
    rw [lowerHessian_eq hg]
    exact lowerHessian_coercive hg hsc x (lowerSolution I x) v
  have hh := mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hL.le)
  simpa [hessian, graph, inner_smul_left, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm] using hh

lemma hessian_inverse_norm {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hL : 0 < p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x : p.X) :
    ‖(hessian I x).inverse‖ ≤ p.L / p.μ := by
  simpa using BilevelCurvature.coercive_inverse_norm (hessian I x) (div_pos hμ hL)
    (hessian_coercive hg hL hsc x)

lemma lift_line_hasDerivAt {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x w a : p.X) :
    HasDerivAt (fun t : ℝ => lift I (x + t • w) a) (0, second I x w a) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w |>.const_add x
  have hs1 : ContDiff ℝ 1 (fderiv ℝ (lowerSolution I)) :=
    (contDiff_succ_iff_fderiv.mp (lowerSolution_contDiff hg hμ hsc)).2.2
  have hd := (hs1.differentiable (by norm_num) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const a x)
  have hh := hd.comp_hasDerivAt_of_eq 0 hl (by simp : x = x + (0 : ℝ) • w)
  have he : HasDerivAt (fun t : ℝ => fderiv ℝ (lowerSolution I) (x + t • w) a)
      (second I x w a) 0 := by simpa [second, Function.comp_def] using hh
  exact (hasDerivAt_const (0 : ℝ) a).prodMk he


lemma changing_third_bound {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hL : 0 < p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hLip : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (hLip3 : ∀ z w, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z -
      fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) w‖ ≤ p.L * ‖z - w‖)
    {q : ℝ} (hq : 1 ≤ q) (heq : p.μ * q ^ 2 = p.L)
    (x w a b : p.X) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (t : ℝ) :
    ‖(hessian I x).inverse ((third I (x + t • w) - third I x)
      (lift I (x + t • w) a) (lift I (x + t • w) b))‖ ≤
      (q ^ 8 * ‖w‖) * |t| := by
  have hratio : p.L / p.μ = q ^ 2 := by rw [← heq]; field_simp
  have hμL : p.μ ≤ p.L := by nlinarith [sq_nonneg (q - 1)]
  have hR : ‖(hessian I x).inverse‖ ≤ q ^ 2 := by
    simpa [hratio] using hessian_inverse_norm hg hμ hL hsc x
  have hT : ‖third I (x + t • w) - third I x‖ ≤ q ^ 2 * (‖w‖ * |t|) := by
    calc
      _ ≤ ‖graph I (x + t • w) - graph I x‖ := third_lipschitz hg hL hLip3 _ _
      _ ≤ (p.L / p.μ) * ‖(x + t • w) - x‖ := graph_lipschitz hg hμ hμL hsc hLip _ _
      _ = _ := by simp [hratio, norm_smul, Real.norm_eq_abs, mul_comm]
  have hunit : ∀ u : p.X, ‖u‖ ≤ 1 → ‖lift I (x + t • w) u‖ ≤ q ^ 2 := by
    intro u hu
    calc
      _ ≤ (p.L / p.μ) * ‖u‖ := lift_norm_bound hg hμ hμL hsc hLip _ _
      _ ≤ q ^ 2 := by rw [hratio]; nlinarith [sq_nonneg q]
  have hh := BilevelTransport.changing_tensor_bound (hessian I x).inverse
    (third I x) (third I (x + t • w)) (lift I (x + t • w) a)
    (lift I (x + t • w) b) (mul_nonneg (norm_nonneg w) (abs_nonneg t))
    hR hT (hunit a ha) (hunit b hb)
  simpa [mul_assoc] using hh

lemma response_transport_norm {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hL : 0 < p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hLip : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (hLip2 : ∀ z w, ‖fderiv ℝ (fderiv ℝ I.g) z - fderiv ℝ (fderiv ℝ I.g) w‖ ≤ p.L * ‖z - w‖)
    (hLip3 : ∀ z w, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z -
      fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) w‖ ≤ p.L * ‖z - w‖)
    {q : ℝ} (hq : 1 ≤ q) (heq : p.μ * q ^ 2 = p.L)
    (x a b w : p.X) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖(hessian I x).inverse (third I x (0, second I x b a) (lift I x w))‖ ≤ 80 * q ^ 8 := by
  let s := (x, lowerSolution I x)
  let H := lowerHessian I s
  let T := p.L⁻¹ • fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) s
  have hsym : ∀ u v, ⟪(p.L⁻¹ • H) u, v⟫ = ⟪(p.L⁻¹ • H) v, u⟫ := by
    intro u v
    simp only [smul_apply, inner_smul_left, conj_trivial]
    rw [lowerHessian_symmetric hg]
  have hpos : ∀ v, 0 ≤ ⟪(p.L⁻¹ • H) v, v⟫ := by
    intro v
    simp only [smul_apply, inner_smul_left, conj_trivial]
    exact mul_nonneg (inv_nonneg.mpr hL.le) (lowerHessian_positive hg hμ.le hsc s v)
  let P := energySeminorm (p.L⁻¹ • H) hsym hpos
  have hP : ∀ v, p.L * (P v) ^ 2 = ⟪H v, v⟫ := by
    intro v
    rw [show P v = Real.sqrt ⟪(p.L⁻¹ • H) v, v⟫ from rfl, Real.sq_sqrt (hpos v)]
    simp only [smul_apply, inner_smul_left, conj_trivial]
    rw [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
  have hy : ‖fderiv ℝ (lowerSolution I) x w‖ ≤ q ^ 2 ∧
      P (fderiv ℝ (lowerSolution I) x w) ≤ q := by
    have hh := lowerSolution_derivative_bounds hg hμ hL.le hsc hLip x w
    apply scaled_response_bounds H P hL hμ (by linarith) heq hP
    · exact hh.1.trans (by nlinarith)
    · exact hh.2.trans (by simpa using mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hw 2) (sq_nonneg p.L))
  have hTnorm : ‖T‖ ≤ 1 := by
    have ht : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) s‖ ≤ p.L :=
      norm_fderiv_le_of_lip' ℝ hL.le (Filter.Eventually.of_forall (fun z => hLip2 z s))
    dsimp [T]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hL.le)]
    calc
      _ ≤ p.L⁻¹ * p.L := mul_le_mul_of_nonneg_left ht (by positivity)
      _ = 1 := inv_mul_cancel₀ hL.ne'
  have hTb : ∀ w u v, |T w u v| ≤ ‖w‖ * ‖u‖ * ‖v‖ := by
    intro w u v
    calc
      _ = ‖T w u v‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖T w u‖ * ‖v‖ := (T w u).le_opNorm v
      _ ≤ (‖T w‖ * ‖u‖) * ‖v‖ := by gcongr; exact (T w).le_opNorm u
      _ ≤ (‖T‖ * ‖w‖ * ‖u‖) * ‖v‖ := by gcongr; exact T.le_opNorm w
      _ ≤ (1 * ‖w‖ * ‖u‖) * ‖v‖ := by gcongr
      _ = _ := by ring
  have hTm : ∀ w u v, |T w (0, u) (0, v)| ≤
      2 * ‖w‖ * (‖u‖ * P v + ‖v‖ * P u) := by
    intro w u v
    have hh := normalized_positive_field_mixed hL (lowerHessian_hasFDerivAt hg)
      (lowerHessian_derivative_lipschitz hLip3) (lowerHessian_positive hg hμ.le hsc)
      (lowerHessian_symmetric hg) s w u v
    simpa only [ContinuousLinearMap.comp_apply, lowerHessianMap_apply,
      lowerRestriction_inner, T, P, energySeminorm_apply, H, smul_apply, smul_eq_mul] using hh
  have hC : ∀ u v r, ⟪third I x u v, r⟫ = T (0, r) u v := by
    intro u v r
    simp only [third, T, smul_apply, inner_smul_left, conj_trivial, smul_eq_mul]
    rw [lowerGradient_second_inner hg]
    rfl
  have hi : (hessian I x).IsInvertible :=
    coercive_isInvertible _ (div_pos hμ hL) (hessian_coercive hg hL hsc x)
  have hR : ∀ u v, ⟪(hessian I x).inverse u, v⟫ = ⟪u, (hessian I x).inverse v⟫ :=
    inverse_inner_swap _ hi hsym
  have hRn : ‖(hessian I x).inverse‖ ≤ q ^ 2 := by
    have hh := hessian_inverse_norm hg hμ hL hsc x
    have he : p.L / p.μ = q ^ 2 := by rw [← heq]; field_simp
    simpa [he] using hh
  have hz := BilevelResponseBounds.second_response_bounds hg hμ hL hsc hLip hLip2 hLip3
    hq heq x a b ha hb
  exact inverse_transport_norm T (third I x) (hessian I x).inverse P hq hTb hTm
    hC hR hRn hw hy.1 hy.2 hz.2 hz.1

lemma hessian_line_hasDerivAt {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x w : p.X) :
    HasDerivAt (fun t : ℝ => hessian I (x + t • w))
      (fderiv ℝ (hessian I) x w) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w |>.const_add x
  have hh := (hessian_hasFDerivAt hg hμ hsc x).comp_hasDerivAt_of_eq 0 hl
    (by simp : x = x + (0 : ℝ) • w)
  rw [← (hessian_hasFDerivAt hg hμ hsc x).fderiv] at hh
  exact hh

lemma third_symmetric {p : Params} {I : Instance p} (hg : ContDiff ℝ 3 I.g)
    (x : p.X) (a b : p.X × p.Y) : third I x a b = third I x b a := by
  have hh := ((lowerGradient_contDiff hg).contDiffAt (x := graph I x)).isSymmSndFDerivAt (by norm_num)
    |>.eq a b
  simpa only [third, smul_apply] using congrArg (fun v : p.Y => p.L⁻¹ • v) hh

lemma total_transport_norm {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hL : 0 < p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hLip : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (hLip2 : ∀ z w, ‖fderiv ℝ (fderiv ℝ I.g) z - fderiv ℝ (fderiv ℝ I.g) w‖ ≤ p.L * ‖z - w‖)
    (hLip3 : ∀ z w, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z -
      fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) w‖ ≤ p.L * ‖z - w‖)
    {q : ℝ} (hq : 1 ≤ q) (heq : p.μ * q ^ 2 = p.L)
    (x a b w : p.X) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖(hessian I x).inverse (third I x (0, second I x w b) (lift I x a) +
      third I x (lift I x b) (0, second I x w a) +
      fderiv ℝ (hessian I) x w (second I x b a))‖ ≤ 240 * q ^ 8 := by
  have h1 := response_transport_norm hg hμ hL hsc hLip hLip2 hLip3 hq heq x b w a hb hw ha
  have h2 := response_transport_norm hg hμ hL hsc hLip hLip2 hLip3 hq heq x a w b ha hw hb
  have h3 := response_transport_norm hg hμ hL hsc hLip hLip2 hLip3 hq heq x a b w ha hb hw
  rw [hessian_derivative_apply hg hμ hsc,
    third_symmetric hg x (lift I x b), third_symmetric hg x (lift I x w), map_add, map_add]
  calc
    _ ≤ ‖(hessian I x).inverse (third I x (0, second I x w b) (lift I x a))‖ +
        ‖(hessian I x).inverse (third I x (0, second I x w a) (lift I x b))‖ +
        ‖(hessian I x).inverse (third I x (0, second I x b a) (lift I x w))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

lemma second_local_slope {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hL : 0 < p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hLip : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (hLip2 : ∀ z w, ‖fderiv ℝ (fderiv ℝ I.g) z - fderiv ℝ (fderiv ℝ I.g) w‖ ≤ p.L * ‖z - w‖)
    (hLip3 : ∀ z w, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z -
      fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) w‖ ≤ p.L * ‖z - w‖)
    {q : ℝ} (hq : 1 ≤ q) (heq : p.μ * q ^ 2 = p.L)
    (x a b w : p.X) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ∀ r : ℝ, 241 * q ^ 8 < r →
      ∀ᶠ t in nhdsWithin (0 : ℝ) ({0}ᶜ),
        ‖t⁻¹ • (second I (x + t • w) b a - second I x b a)‖ < r := by
  intro r hr
  let H := fun t : ℝ => hessian I (x + t • w)
  let T := fun t : ℝ => third I (x + t • w)
  let U := fun t : ℝ => lift I (x + t • w) b
  let V := fun t : ℝ => lift I (x + t • w) a
  let Z := fun t : ℝ => second I (x + t • w) b a
  let R := (hessian I x).inverse
  have hi : (hessian I x).IsInvertible :=
    coercive_isInvertible _ (div_pos hμ hL) (hessian_coercive hg hL hsc x)
  have hR : ∀ v, R (H 0 v) = v := by
    intro v
    simpa [R, H] using hi.inverse_apply_self v
  have hroot : ∀ t, H t (Z t) = -T t (U t) (V t) := by
    intro t
    exact normalized_root_identity hg hμ hsc _ a b
  have hZ : ContinuousAt Z 0 := by
    have hc := second_continuous hg hμ hsc
    dsimp [Z]
    fun_prop
  have hA : ∀ t, t ≠ 0 → ‖R ((T t - T 0) (U t) (V t))‖ ≤ q ^ 8 * |t| := by
    intro t _
    have hh := changing_third_bound hg hμ hL hsc hLip hLip3 hq heq x w b a hb ha t
    have hle : (q ^ 8 * ‖w‖) * |t| ≤ q ^ 8 * |t| := by
      calc
        _ ≤ (q ^ 8 * 1) * |t| := by gcongr
        _ = _ := by ring
    simpa [R, T, U, V] using hh.trans hle
  have hB : ‖R (T 0 (0, second I x w b) (V 0) +
      T 0 (U 0) (0, second I x w a) + fderiv ℝ (hessian I) x w (Z 0))‖ ≤ 240 * q ^ 8 := by
    simpa [R, T, U, V, Z] using
      total_transport_norm hg hμ hL hsc hLip hLip2 hLip3 hq heq x a b w ha hb hw
  have hh := BilevelTransport.local_slope_bound R hR hroot
    (lift_line_hasDerivAt hg hμ hsc x w b) (lift_line_hasDerivAt hg hμ hsc x w a)
    (hessian_line_hasDerivAt hg hμ hsc x w) hZ hA hB (by linarith : q ^ 8 + 240 * q ^ 8 < r)
  simpa [Z] using hh

lemma second_lipschitz {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hL : 0 < p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hLip : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (hLip2 : ∀ z w, ‖fderiv ℝ (fderiv ℝ I.g) z - fderiv ℝ (fderiv ℝ I.g) w‖ ≤ p.L * ‖z - w‖)
    (hLip3 : ∀ z w, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z -
      fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) w‖ ≤ p.L * ‖z - w‖)
    {q : ℝ} (hq : 1 ≤ q) (heq : p.μ * q ^ 2 = p.L)
    (x y : p.X) : ‖second I x - second I y‖ ≤ 241 * q ^ 8 * ‖x - y‖ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro b hb
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro a ha
  have hc : Continuous (fun z : p.X => second I z b a) := by
    have hh := second_continuous hg hμ hsc
    fun_prop
  have hh := BilevelImplicit.norm_sub_le_of_unit_local_slope hc
    (fun z w hw r hr => second_local_slope hg hμ hL hsc hLip hLip2 hLip3 hq heq
      z a b w (le_of_eq ha) (le_of_eq hb) hw r hr) y x
  simpa only [sub_apply] using hh

lemma first_lipschitz {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hL : 0 < p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hLip : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (hLip2 : ∀ z w, ‖fderiv ℝ (fderiv ℝ I.g) z - fderiv ℝ (fderiv ℝ I.g) w‖ ≤ p.L * ‖z - w‖)
    (hLip3 : ∀ z w, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z -
      fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) w‖ ≤ p.L * ‖z - w‖)
    {q : ℝ} (hq : 1 ≤ q) (heq : p.μ * q ^ 2 = p.L)
    (x y : p.X) : ‖fderiv ℝ (lowerSolution I) x - fderiv ℝ (lowerSolution I) y‖ ≤
      (16 * q ^ 5) * ‖x - y‖ := by
  have hs1 : ContDiff ℝ 1 (fderiv ℝ (lowerSolution I)) :=
    (contDiff_succ_iff_fderiv.mp (lowerSolution_contDiff hg hμ hsc)).2.2
  have hb : ∀ z, ‖fderiv ℝ (fderiv ℝ (lowerSolution I)) z‖ ≤ 16 * q ^ 5 := by
    intro z
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro b hb
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro a ha
    exact (BilevelResponseBounds.second_response_bounds hg hμ hL hsc hLip hLip2 hLip3
      hq heq z a b ha.le hb.le).2
  have hh := lipschitzWith_of_nnnorm_fderiv_le (C := ⟨16 * q ^ 5, by positivity⟩)
    (hs1.differentiable (by norm_num))
    (fun z => show ‖fderiv ℝ (fderiv ℝ (lowerSolution I)) z‖₊ ≤ ⟨16 * q ^ 5, by positivity⟩ from hb z)
  exact hh.norm_sub_le x y

end LongTails.Proofs.BilevelResponseTransport
