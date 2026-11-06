import LongTails.Proofs.BilevelResponseTransport

set_option maxSynthPendingDepth 5

namespace LongTails.Proofs.BilevelHyperobjective

open LongTails.Setups.HigherSmoothBilevel BilevelGeometry BilevelResponseBounds
open scoped RealInnerProductSpace

lemma gradient_norm_bound {p : Params} {I : Instance p}
    (hf : Differentiable ℝ I.f) (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hL : 0 < p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hf0 : ∀ z, ‖fderiv ℝ I.f z‖ ≤ p.L)
    (hLip : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    {q : ℝ} (hq : 1 ≤ q) (heq : p.μ * q ^ 2 = p.L) (x : p.X) :
    ‖gradient (hyperObjective I) x‖ ≤ p.L * q ^ 2 := by
  have hnorm : ‖fderiv ℝ (hyperObjective I) x‖ ≤ p.L * q ^ 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro a ha
    have hY := (lowerSolution_derivative_bounds hg hμ hL.le hsc hLip x a).1
    rw [ha, mul_one] at hY
    have hn : ‖fderiv ℝ (lowerSolution I) x a‖ ≤ q ^ 2 := by nlinarith
    have hv : ‖(a, fderiv ℝ (lowerSolution I) x a)‖ ≤ q ^ 2 := by
      simp only [Prod.norm_mk, ha]
      exact max_le (by nlinarith) hn
    rw [show fderiv ℝ (hyperObjective I) x a =
        fderiv ℝ I.f (x, lowerSolution I x) (a, fderiv ℝ (lowerSolution I) x a) from
      BilevelImplicit.graph_composite_first hf
        ((lowerSolution_contDiff hg hμ hsc).differentiable (by norm_num)) x a]
    exact ((fderiv ℝ I.f (x, lowerSolution I x)).le_opNorm _).trans
      (mul_le_mul (hf0 _) hv (norm_nonneg _) hL.le)
  simpa only [gradient, LinearIsometryEquiv.norm_map] using hnorm

lemma hessian_norm_bound {p : Params} {I : Instance p}
    (hf : ContDiff ℝ 2 I.f) (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hL : 0 < p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hf0 : ∀ z, ‖fderiv ℝ I.f z‖ ≤ p.L)
    (hf1 : ∀ z w, ‖fderiv ℝ I.f z - fderiv ℝ I.f w‖ ≤ p.L * ‖z - w‖)
    (hLip : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (hLip2 : ∀ z w, ‖fderiv ℝ (fderiv ℝ I.g) z - fderiv ℝ (fderiv ℝ I.g) w‖ ≤ p.L * ‖z - w‖)
    (hLip3 : ∀ z w, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z -
      fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) w‖ ≤ p.L * ‖z - w‖)
    {q : ℝ} (hq : 1 ≤ q) (heq : p.μ * q ^ 2 = p.L) (x : p.X) :
    ‖fderiv ℝ (fderiv ℝ (hyperObjective I)) x‖ ≤ 32 * p.L * q ^ 5 := by
  have hq0 : 0 ≤ q := by linarith
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro b hb
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro a ha
  let s := (x, lowerSolution I x)
  let Y := fderiv ℝ (lowerSolution I) x
  let Z := fderiv ℝ (fderiv ℝ (lowerSolution I)) x b a
  have hy : ∀ u : p.X, ‖u‖ = 1 → ‖(u, Y u)‖ ≤ q ^ 2 := by
    intro u hu
    have hh := (lowerSolution_derivative_bounds hg hμ hL.le hsc hLip x u).1
    have hYu : ‖Y u‖ ≤ q ^ 2 := by rw [hu] at hh; dsimp [Y]; nlinarith
    simp only [Prod.norm_mk, hu]
    exact max_le (by nlinarith) hYu
  have hz : ‖Z‖ ≤ 16 * q ^ 5 :=
    (second_response_bounds hg hμ hL hsc hLip hLip2 hLip3 hq heq x a b ha.le hb.le).2
  have hf2 : ‖fderiv ℝ (fderiv ℝ I.f) s‖ ≤ p.L :=
    norm_fderiv_le_of_lip' ℝ hL.le (Filter.Eventually.of_forall (fun z => hf1 z s))
  have hchain := BilevelImplicit.graph_composite_second hf (lowerSolution_contDiff hg hμ hsc) x a b
  change fderiv ℝ (fderiv ℝ (hyperObjective I)) x b a = _ at hchain
  rw [hchain]
  change ‖fderiv ℝ (fderiv ℝ I.f) s (b, Y b) (a, Y a) + fderiv ℝ I.f s (0, Z)‖ ≤ _
  have hfirst : ‖fderiv ℝ (fderiv ℝ I.f) s (b, Y b) (a, Y a)‖ ≤ p.L * q ^ 4 := by
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ I.f) s (b, Y b)‖ * ‖(a, Y a)‖ :=
        (fderiv ℝ (fderiv ℝ I.f) s (b, Y b)).le_opNorm _
      _ ≤ (‖fderiv ℝ (fderiv ℝ I.f) s‖ * ‖(b, Y b)‖) * ‖(a, Y a)‖ := by
        gcongr
        exact (fderiv ℝ (fderiv ℝ I.f) s).le_opNorm _
      _ ≤ (p.L * q ^ 2) * q ^ 2 := by gcongr; exact hy b hb; exact hy a ha
      _ = _ := by ring
  have hsecond : ‖fderiv ℝ I.f s (0, Z)‖ ≤ 16 * p.L * q ^ 5 := by
    calc
      _ ≤ ‖fderiv ℝ I.f s‖ * ‖((0 : p.X), Z)‖ := (fderiv ℝ I.f s).le_opNorm _
      _ = ‖fderiv ℝ I.f s‖ * ‖Z‖ := by simp
      _ ≤ p.L * (16 * q ^ 5) := mul_le_mul (hf0 s) hz (norm_nonneg _) hL.le
      _ = _ := by ring
  have hq45 : q ^ 4 ≤ q ^ 5 := by
    calc q ^ 4 = q ^ 4 * 1 := by ring
      _ ≤ q ^ 4 * q := mul_le_mul_of_nonneg_left hq (by positivity)
      _ = q ^ 5 := by ring
  have hlast := mul_le_mul_of_nonneg_left hq45 hL.le
  exact (norm_add_le _ _).trans (by nlinarith [hfirst, hsecond, mul_nonneg hL.le (pow_nonneg hq0 5)])

lemma bilinear_difference_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A B : E →L[ℝ] E →L[ℝ] F) (u v s t : E) :
    ‖A u v - B s t‖ ≤ ‖A - B‖ * ‖u‖ * ‖v‖ +
      ‖B‖ * ‖u - s‖ * ‖v‖ + ‖B‖ * ‖s‖ * ‖v - t‖ := by
  have he : A u v - B s t = (A - B) u v + B (u - s) v + B s (v - t) := by
    simp only [sub_apply, map_sub]
    abel
  have hb : ∀ (C : E →L[ℝ] E →L[ℝ] F) (a b : E),
      ‖C a b‖ ≤ ‖C‖ * ‖a‖ * ‖b‖ := by
    intro C a b
    exact ((C a).le_opNorm b).trans
      (mul_le_mul_of_nonneg_right (C.le_opNorm a) (norm_nonneg b))
  rw [he]
  calc
    _ ≤ ‖(A - B) u v‖ + ‖B (u - s) v‖ + ‖B s (v - t)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add (hb _ _ _) (hb _ _ _)) (hb _ _ _)

lemma hessian_lipschitz {p : Params} {I : Instance p}
    (hf : ContDiff ℝ 2 I.f) (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hL : 0 < p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hf0 : ∀ z, ‖fderiv ℝ I.f z‖ ≤ p.L)
    (hf1 : ∀ z w, ‖fderiv ℝ I.f z - fderiv ℝ I.f w‖ ≤ p.L * ‖z - w‖)
    (hf2 : ∀ z w, ‖fderiv ℝ (fderiv ℝ I.f) z - fderiv ℝ (fderiv ℝ I.f) w‖ ≤ p.L * ‖z - w‖)
    (hLip : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (hLip2 : ∀ z w, ‖fderiv ℝ (fderiv ℝ I.g) z - fderiv ℝ (fderiv ℝ I.g) w‖ ≤ p.L * ‖z - w‖)
    (hLip3 : ∀ z w, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z -
      fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) w‖ ≤ p.L * ‖z - w‖)
    {q : ℝ} (hq : 1 ≤ q) (heq : p.μ * q ^ 2 = p.L) (x y : p.X) :
    ‖fderiv ℝ (fderiv ℝ (hyperObjective I)) x - fderiv ℝ (fderiv ℝ (hyperObjective I)) y‖ ≤
      512 * p.L * q ^ 8 * ‖x - y‖ := by
  have hq0 : 0 ≤ q := by linarith
  have hratio : p.L / p.μ = q ^ 2 := by rw [← heq]; field_simp
  have hμL : p.μ ≤ p.L := by nlinarith [sq_nonneg (q - 1)]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro b hb
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro a ha
  let sx := BilevelResponseTransport.graph I x
  let sy := BilevelResponseTransport.graph I y
  let V := BilevelResponseTransport.lift I
  let Z := BilevelResponseTransport.second I
  have hgraph : ‖sx - sy‖ ≤ q ^ 2 * ‖x - y‖ := by
    simpa [sx, sy, hratio] using BilevelResponseTransport.graph_lipschitz hg hμ hμL hsc hLip x y
  have hV : ∀ z u, ‖u‖ = 1 → ‖V z u‖ ≤ q ^ 2 := by
    intro z u hu
    simpa [V, hratio, hu] using BilevelResponseTransport.lift_norm_bound hg hμ hμL hsc hLip z u
  have hVdiff : ∀ u, ‖u‖ = 1 → ‖V x u - V y u‖ ≤ 16 * q ^ 5 * ‖x - y‖ := by
    intro u hu
    have hh := BilevelResponseTransport.first_lipschitz hg hμ hL hsc hLip hLip2 hLip3 hq heq x y
    have hn := (fderiv ℝ (lowerSolution I) x - fderiv ℝ (lowerSolution I) y).le_opNorm u
    simpa [V, BilevelResponseTransport.lift, hu] using hn.trans (by simpa [hu] using hh)
  have hZ : ‖Z x b a‖ ≤ 16 * q ^ 5 :=
    (second_response_bounds hg hμ hL hsc hLip hLip2 hLip3 hq heq x a b ha.le hb.le).2
  have hZdiff : ‖Z x b a - Z y b a‖ ≤ 241 * q ^ 8 * ‖x - y‖ := by
    have hh := BilevelResponseTransport.second_lipschitz hg hμ hL hsc hLip hLip2 hLip3 hq heq x y
    have h1 := (Z x - Z y).le_opNorm b
    have h2 := ((Z x - Z y) b).le_opNorm a
    rw [hb, mul_one] at h1
    rw [ha, mul_one] at h2
    exact h2.trans (h1.trans hh)
  have hfn : ‖fderiv ℝ (fderiv ℝ I.f) sy‖ ≤ p.L :=
    norm_fderiv_le_of_lip' ℝ hL.le (Filter.Eventually.of_forall (fun z => hf1 z sy))
  have hfd : ‖fderiv ℝ (fderiv ℝ I.f) sx - fderiv ℝ (fderiv ℝ I.f) sy‖ ≤
      p.L * q ^ 2 * ‖x - y‖ := (hf2 sx sy).trans (by nlinarith)
  have hfirst : ‖fderiv ℝ (fderiv ℝ I.f) sx (V x b) (V x a) -
      fderiv ℝ (fderiv ℝ I.f) sy (V y b) (V y a)‖ ≤
      p.L * (q ^ 6 + 32 * q ^ 7) * ‖x - y‖ := by
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ I.f) sx - fderiv ℝ (fderiv ℝ I.f) sy‖ * ‖V x b‖ * ‖V x a‖ +
          ‖fderiv ℝ (fderiv ℝ I.f) sy‖ * ‖V x b - V y b‖ * ‖V x a‖ +
          ‖fderiv ℝ (fderiv ℝ I.f) sy‖ * ‖V y b‖ * ‖V x a - V y a‖ :=
        bilinear_difference_bound _ _ _ _ _ _
      _ ≤ (p.L * q ^ 2 * ‖x - y‖) * q ^ 2 * q ^ 2 +
          p.L * (16 * q ^ 5 * ‖x - y‖) * q ^ 2 +
          p.L * q ^ 2 * (16 * q ^ 5 * ‖x - y‖) := by
        gcongr <;> first | exact hV _ _ ha | exact hV _ _ hb | exact hVdiff _ ha | exact hVdiff _ hb
      _ = _ := by ring
  have hfd1 : ‖fderiv ℝ I.f sx - fderiv ℝ I.f sy‖ ≤ p.L * q ^ 2 * ‖x - y‖ :=
    (hf1 sx sy).trans (by nlinarith)
  have he : fderiv ℝ I.f sx (0, Z x b a) - fderiv ℝ I.f sy (0, Z y b a) =
      (fderiv ℝ I.f sx - fderiv ℝ I.f sy) (0, Z x b a) +
      fderiv ℝ I.f sy (0, Z x b a - Z y b a) := by
    simp only [sub_apply]
    rw [show ((0 : p.X), Z x b a - Z y b a) = (0, Z x b a) - (0, Z y b a) by simp, map_sub]
    abel
  have hsecond : ‖fderiv ℝ I.f sx (0, Z x b a) - fderiv ℝ I.f sy (0, Z y b a)‖ ≤
      p.L * (16 * q ^ 7 + 241 * q ^ 8) * ‖x - y‖ := by
    rw [he]
    calc
      _ ≤ ‖(fderiv ℝ I.f sx - fderiv ℝ I.f sy) (0, Z x b a)‖ +
          ‖fderiv ℝ I.f sy (0, Z x b a - Z y b a)‖ := norm_add_le _ _
      _ ≤ ‖fderiv ℝ I.f sx - fderiv ℝ I.f sy‖ * ‖Z x b a‖ +
          ‖fderiv ℝ I.f sy‖ * ‖Z x b a - Z y b a‖ := by
        apply add_le_add
        · simpa using (fderiv ℝ I.f sx - fderiv ℝ I.f sy).le_opNorm ((0 : p.X), Z x b a)
        · simpa using (fderiv ℝ I.f sy).le_opNorm ((0 : p.X), Z x b a - Z y b a)
      _ ≤ (p.L * q ^ 2 * ‖x - y‖) * (16 * q ^ 5) +
          p.L * (241 * q ^ 8 * ‖x - y‖) := by gcongr; exact hf0 sy
      _ = _ := by ring
  have hx := BilevelImplicit.graph_composite_second hf (lowerSolution_contDiff hg hμ hsc) x a b
  have hy := BilevelImplicit.graph_composite_second hf (lowerSolution_contDiff hg hμ hsc) y a b
  change fderiv ℝ (fderiv ℝ (hyperObjective I)) x b a = _ at hx
  change fderiv ℝ (fderiv ℝ (hyperObjective I)) y b a = _ at hy
  simp only [sub_apply]
  rw [hx, hy, add_sub_add_comm]
  have hh := (norm_add_le _ _).trans (add_le_add hfirst hsecond)
  have hp6 : q ^ 6 ≤ q ^ 8 := pow_le_pow_right₀ hq (by norm_num)
  have hp7 : q ^ 7 ≤ q ^ 8 := pow_le_pow_right₀ hq (by norm_num)
  apply hh.trans
  have hc : q ^ 6 + 32 * q ^ 7 + (16 * q ^ 7 + 241 * q ^ 8) ≤ 512 * q ^ 8 := by nlinarith [pow_nonneg hq0 8]
  have hc' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hL.le) (norm_nonneg (x - y))
  nlinarith only [hc']

lemma gradient_lipschitz {p : Params} {I : Instance p}
    (hf : ContDiff ℝ 2 I.f) (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hL : 0 < p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hf0 : ∀ z, ‖fderiv ℝ I.f z‖ ≤ p.L)
    (hf1 : ∀ z w, ‖fderiv ℝ I.f z - fderiv ℝ I.f w‖ ≤ p.L * ‖z - w‖)
    (hLip : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (hLip2 : ∀ z w, ‖fderiv ℝ (fderiv ℝ I.g) z - fderiv ℝ (fderiv ℝ I.g) w‖ ≤ p.L * ‖z - w‖)
    (hLip3 : ∀ z w, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z -
      fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) w‖ ≤ p.L * ‖z - w‖)
    {q : ℝ} (hq : 1 ≤ q) (heq : p.μ * q ^ 2 = p.L) (x y : p.X) :
    ‖gradient (hyperObjective I) x - gradient (hyperObjective I) y‖ ≤
      (32 * p.L * q ^ 5) * ‖x - y‖ := by
  have hF := hyperObjective_contDiff hf hg hμ hsc
  have hF1 : ContDiff ℝ 1 (fderiv ℝ (hyperObjective I)) :=
    (contDiff_succ_iff_fderiv.mp hF).2.2
  have hh := lipschitzWith_of_nnnorm_fderiv_le (C := ⟨32 * p.L * q ^ 5, by positivity⟩)
    (hF1.differentiable (by norm_num))
    (fun z => show ‖fderiv ℝ (fderiv ℝ (hyperObjective I)) z‖₊ ≤ ⟨32 * p.L * q ^ 5, by positivity⟩ from
      hessian_norm_bound hf hg hμ hL hsc hf0 hf1 hLip hLip2 hLip3 hq heq z)
  have hd : ‖fderiv ℝ (hyperObjective I) x - fderiv ℝ (hyperObjective I) y‖ ≤
      (32 * p.L * q ^ 5) * ‖x - y‖ := hh.norm_sub_le x y
  unfold gradient
  rw [← map_sub, LinearIsometryEquiv.norm_map]
  exact hd

lemma gradient_jacobian_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    fderiv ℝ (gradient f) x = (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.comp
      (fderiv ℝ (fderiv ℝ f) x) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := (contDiff_succ_iff_fderiv.mp hf).2.2
  exact ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.hasFDerivAt.comp x
    (hd.differentiable (by norm_num) x).hasFDerivAt).fderiv

lemma gradient_jacobian_sub_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x y : E) :
    ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ := by
  rw [gradient_jacobian_eq hf, gradient_jacobian_eq hf, ← ContinuousLinearMap.comp_sub]
  have hn : ‖(InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    simp
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg _))

lemma gradient_jacobian_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    ‖fderiv ℝ (gradient f) x‖ ≤ ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  rw [gradient_jacobian_eq hf]
  have hn : ‖(InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    simp
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg _))

end LongTails.Proofs.BilevelHyperobjective
