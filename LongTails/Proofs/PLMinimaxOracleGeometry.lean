import LongTails.Setups.NonconvexPLSecondOrder
import LongTails.Proofs.PLMinimaxEnvelope
import LongTails.Proofs.CubicRegularization
import LongTails.Proofs.PLMinimaxResolvent
import LongTails.Proofs.SpectralGradientModel

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.PLMinimax

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

lemma joint_gradient_fst {f : WithLp 2 (E × F) → ℝ} {g : WithLp 2 (E × F)}
    {x : E} {y : F} (hg : HasGradientAt f g (WithLp.toLp 2 (x, y))) :
    HasGradientAt (fun x => f (WithLp.toLp 2 (x, y))) g.fst x := by
  let A : E →L[ℝ] WithLp 2 (E × F) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ E F)
  have hA : HasFDerivAt (fun x => A x + WithLp.toLp 2 (0, y)) A x :=
    A.hasFDerivAt.add_const _
  have he : (fun x => A x + WithLp.toLp 2 (0, y)) = (fun x => WithLp.toLp 2 (x, y)) := by
    funext x
    change WithLp.toLp 2 (x, 0) + WithLp.toLp 2 (0, y) = _
    rw [← WithLp.toLp_add]
    simp
  rw [he] at hA
  have hh := hg.hasFDerivAt.comp x hA
  rw [hasGradientAt_iff_hasFDerivAt]
  have heq : toDual ℝ E g.fst = (toDual ℝ (WithLp 2 (E × F)) g).comp A := by
    ext v
    change ⟪g.fst, v⟫ = ⟪g, WithLp.toLp 2 (v, 0)⟫
    simp [WithLp.prod_inner_apply]
  rw [heq]
  exact hh

lemma joint_gradient_snd {f : WithLp 2 (E × F) → ℝ} {g : WithLp 2 (E × F)}
    {x : E} {y : F} (hg : HasGradientAt f g (WithLp.toLp 2 (x, y))) :
    HasGradientAt (fun y => f (WithLp.toLp 2 (x, y))) g.snd y := by
  let A : F →L[ℝ] WithLp 2 (E × F) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ E F)
  have hA : HasFDerivAt (fun y => A y + WithLp.toLp 2 (x, 0)) A y :=
    A.hasFDerivAt.add_const _
  have he : (fun y => A y + WithLp.toLp 2 (x, 0)) = (fun y => WithLp.toLp 2 (x, y)) := by
    funext y
    change WithLp.toLp 2 (0, y) + WithLp.toLp 2 (x, 0) = _
    rw [← WithLp.toLp_add]
    simp
  rw [he] at hA
  have hh := hg.hasFDerivAt.comp y hA
  rw [hasGradientAt_iff_hasFDerivAt]
  have heq : toDual ℝ F g.snd = (toDual ℝ (WithLp 2 (E × F)) g).comp A := by
    ext v
    change ⟪g.snd, v⟫ = ⟪g, WithLp.toLp 2 (0, v)⟫
    simp [WithLp.prod_inner_apply]
  rw [heq]
  exact hh

omit [InnerProductSpace ℝ E] [CompleteSpace E] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma joint_norm_le (w : WithLp 2 (E × F)) : ‖w‖ ≤ ‖w.fst‖ + ‖w.snd‖ := by
  have hh := WithLp.prod_norm_sq_eq_of_L2 w
  nlinarith [norm_nonneg w, norm_nonneg w.fst, norm_nonneg w.snd,
    mul_nonneg (norm_nonneg w.fst) (norm_nonneg w.snd)]

lemma setup_hyp {p : LongTails.Setups.NonconvexPLSecondOrder.Params}
    {f : LongTails.Setups.NonconvexPLSecondOrder.Space p → ℝ} {oracle}
    (hv : LongTails.Setups.NonconvexPLSecondOrder.spec.valid p)
    (hf : LongTails.Setups.NonconvexPLSecondOrder.spec.admissible p f oracle) :
    Hyp (fun x y => f (WithLp.toLp 2 (x, y)))
      (fun x y => (gradient f (WithLp.toLp 2 (x, y))).fst)
      (fun x y => (gradient f (WithLp.toLp 2 (x, y))).snd) p.L p.μ := by
  obtain ⟨hμ, hμL, _⟩ := hv
  obtain ⟨hg, _, hl, _, ha, hp, _⟩ := hf
  have hL : 0 < p.L := lt_of_lt_of_le hμ hμL
  refine ⟨hL, hμ, hμL, ?_, ?_, ?_, ?_, ?_, ha⟩
  · intro x y
    exact joint_gradient_fst (hg _)
  · intro x y
    exact joint_gradient_snd (hg _)
  · intro x x' y y'
    have hb := WithLp.norm_fst_le p.E (gradient f (WithLp.toLp 2 (x, y)) -
      gradient f (WithLp.toLp 2 (x', y')))
    have hn := joint_norm_le (WithLp.toLp 2 (x, y) - WithLp.toLp 2 (x', y'))
    exact hb.trans ((hl _ _).trans (mul_le_mul_of_nonneg_left hn hL.le))
  · intro x x' y y'
    have hb := WithLp.norm_snd_le p.E (gradient f (WithLp.toLp 2 (x, y)) -
      gradient f (WithLp.toLp 2 (x', y')))
    have hn := joint_norm_le (WithLp.toLp 2 (x, y) - WithLp.toLp 2 (x', y'))
    exact hb.trans ((hl _ _).trans (mul_le_mul_of_nonneg_left hn hL.le))
  · intro x y y'
    have hm : f (WithLp.toLp 2 (x, y')) ≤ LongTails.Setups.NonconvexPLSecondOrder.value f x := by
      obtain ⟨v, hv⟩ := ha x
      apply le_csSup
      · exact ⟨f (WithLp.toLp 2 (x, v)), by rintro _ ⟨w, rfl⟩; exact hv w⟩
      · exact ⟨y', rfl⟩
    nlinarith [hp x y]

lemma hessian_nonpos_of_line_max {f : E → ℝ} {g : E → E} {H : E → E →L[ℝ] E}
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : ∀ x, HasFDerivAt g (H x) x)
    (hH : ∀ x y, ‖H x - H y‖ ≤ ρ * ‖x - y‖)
    (x d : E) (hgrad : ⟪g x, d⟫ = 0) (hm : ∀ t : ℝ, f (x + t • d) ≤ f x) :
    ⟪d, H x d⟫ ≤ 0 := by
  by_contra ha
  have ha' : 0 < ⟪d, H x d⟫ := lt_of_not_ge ha
  let c := ρ * ‖d‖ ^ 3 + 1
  have hc : 0 < c := by dsimp [c]; positivity
  let t := ⟪d, H x d⟫ / c
  have ht : 0 < t := div_pos ha' hc
  have he : t * c = ⟪d, H x d⟫ := div_mul_cancel₀ _ hc.ne'
  have hh := LongTails.Proofs.CubicRegularization.objective_taylor
    (fun x => (hf x).hasFDerivAt) hg hH x (t • d)
  simp only [inner_smul_right, hgrad, mul_zero, sub_zero, map_smul, real_inner_smul_left,
    norm_smul, Real.norm_of_nonneg ht.le] at hh
  have hb := (abs_le.mp hh).1
  have hm' := hm t
  have hsq : 0 < t ^ 2 := sq_pos_of_pos ht
  have hineq : ⟪d, H x d⟫ ≤ ρ * ‖d‖ ^ 3 * t / 3 := by
    apply le_of_mul_le_mul_left (a := t ^ 2) _ hsq
    nlinarith
  dsimp [c] at he
  nlinarith

omit [CompleteSpace E] [CompleteSpace F] in
lemma primalBlock_apply (w : WithLp 2 (E × F)) :
    primalBlock w = WithLp.toLp 2 (w.fst, 0) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
lemma regularizedHessian_kernel (H : WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F))
    {L : ℝ} (hL : 0 < L) (hs : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫)
    (hbound : ∀ u, ‖H u‖ ≤ L * ‖u‖)
    (hdual : ∀ b : F, ⟪H (WithLp.toLp 2 (0, b)), WithLp.toLp 2 (0, b)⟫ ≤ 0)
    (v : WithLp 2 (E × F)) (hv : regularizedHessian H L v = 0) : v.fst = 0 := by
  let a : WithLp 2 (E × F) := WithLp.toLp 2 (v.fst, 0)
  let b : WithLp 2 (E × F) := WithLp.toLp 2 (0, v.snd)
  have he : a + b = v := by
    change WithLp.toLp 2 (v.fst, 0) + WithLp.toLp 2 (0, v.snd) = v
    rw [← WithLp.toLp_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
    exact (WithLp.equiv 2 (E × F)).left_inv v
  have hz : H (a + b) + (2 * L) • a = 0 := by
    rw [he]
    exact hv
  have ha := kernel_primal_component H hL hs a b
    (by simp [a, b, WithLp.prod_inner_apply]) (hbound a) (hdual v.snd) hz
  exact congrArg WithLp.fst ha

omit [CompleteSpace E] [CompleteSpace F] in
lemma regularizedGradient_taylor
    {g : WithLp 2 (E × F) → WithLp 2 (E × F)}
    {H : WithLp 2 (E × F) → WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F)} {ρ : ℝ}
    (hg : ∀ w, HasFDerivAt g (H w) w)
    (hH : ∀ w v, ‖H w - H v‖ ≤ ρ * ‖w - v‖)
    (L : ℝ) (z : E) (w : WithLp 2 (E × F)) (hw : regularizedGradient g L z w = 0)
    (d : WithLp 2 (E × F)) :
    ‖regularizedGradient g L z (w + d) - regularizedHessian (H w) L d‖ ≤ ρ * ‖d‖ ^ 2 / 2 := by
  have he : regularizedGradient g L z (w + d) - regularizedHessian (H w) L d =
      g (w + d) - g w - H w d := by
    have hh : regularizedGradient g L z (w + d) =
        g (w + d) - g w + regularizedGradient g L z w + (2 * L) • primalBlock d := by
      simp only [regularizedGradient, primalBlock_apply]
      apply WithLp.ofLp_injective 2
      apply Prod.ext <;> simp [smul_add, smul_sub]
      abel
    rw [hh, hw, add_zero]
    simp only [regularizedHessian, add_apply, smul_apply]
    abel
  rw [he]
  exact LongTails.Proofs.CubicRegularization.gradient_taylor hg hH w d

lemma regularizedGradient_root [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F → ℝ} {g : WithLp 2 (E × F) → WithLp 2 (E × F)} {L μ : ℝ}
    (H : Hyp f (fun x y => (g (WithLp.toLp 2 (x, y))).fst)
      (fun x y => (g (WithLp.toLp 2 (x, y))).snd) L μ)
    (z : E) (y : F) (hy : ∀ v, f (primal f L z) v ≤ f (primal f L z) y) :
    regularizedGradient g L z (WithLp.toLp 2 (primal f L z, y)) = 0 := by
  have hx := H.primal_stationary z
  rw [(H.value_hasGradient hy).gradient] at hx
  have hy' := H.max_gradient_zero hy
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact hx
  · simpa [regularizedGradient] using hy'

omit [CompleteSpace E] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma regularizedGradient_center_shift
    (g : WithLp 2 (E × F) → WithLp 2 (E × F)) (L : ℝ) (z h : E) (w : WithLp 2 (E × F)) :
    regularizedGradient g L z w = regularizedGradient g L (z + h) w +
      WithLp.toLp 2 ((2 * L) • h, 0) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;> simp [regularizedGradient, smul_add, smul_sub]
  abel

lemma regularized_roots_move [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F → ℝ} {g : WithLp 2 (E × F) → WithLp 2 (E × F)} {L μ : ℝ}
    (H : Hyp f (fun x y => (g (WithLp.toLp 2 (x, y))).fst)
      (fun x y => (g (WithLp.toLp 2 (x, y))).snd) L μ)
    (z : E) (y : F) (hy : ∀ v, f (primal f L z) v ≤ f (primal f L z) y) (h : E) :
    ∃ q, regularizedGradient g L z q = WithLp.toLp 2 ((2 * L) • h, 0) ∧
      ‖q - WithLp.toLp 2 (primal f L z, y)‖ ≤ Real.sqrt (4 + 32 * L / μ) * ‖h‖ := by
  obtain ⟨v, hv, _, hd, hx⟩ := H.nearby_saddle z (z + h) y hy
  simp only [add_sub_cancel_left] at hd hx
  let q := WithLp.toLp 2 (primal f L (z + h), v)
  refine ⟨q, ?_, ?_⟩
  · rw [regularizedGradient_center_shift g L z h q, regularizedGradient_root H (z + h) v hv,
      zero_add]
  · have hd' : ‖y - v‖ ^ 2 ≤ (32 * L / μ) * ‖h‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ H.hμ]
      nlinarith
    have hx' := pow_le_pow_left₀ (norm_nonneg _) hx 2
    have he := WithLp.prod_norm_sq_eq_of_L2 (q - WithLp.toLp 2 (primal f L z, y))
    change ‖q - WithLp.toLp 2 (primal f L z, y)‖ ^ 2 =
      ‖primal f L (z + h) - primal f L z‖ ^ 2 + ‖v - y‖ ^ 2 at he
    rw [norm_sub_rev v y] at he
    have hc : 0 ≤ 4 + 32 * L / μ := by have := H.hL; have := H.hμ; positivity
    have hs := Real.sq_sqrt hc
    have hn := Real.sqrt_nonneg (4 + 32 * L / μ)
    nlinarith [norm_nonneg (q - WithLp.toLp 2 (primal f L z, y)), norm_nonneg h,
      mul_nonneg hn (norm_nonneg h)]

lemma regularized_primal_error [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F → ℝ} {g : WithLp 2 (E × F) → WithLp 2 (E × F)} {L μ : ℝ}
    (H : Hyp f (fun x y => (g (WithLp.toLp 2 (x, y))).fst)
      (fun x y => (g (WithLp.toLp 2 (x, y))).snd) L μ)
    (z x : E) (y : F) :
    ‖x - primal f L z‖ ≤ ‖regularizedGradient g L z (WithLp.toLp 2 (x, y))‖ /
      Real.sqrt (L * μ) := by
  have hw := H.weighted_primal_residual z x y
  have hpos : 0 < L * μ := mul_pos H.hL H.hμ
  have hd : L * μ ≤ L ^ 2 := by nlinarith [H.hμL, H.hL]
  have ht := div_le_div_of_nonneg_left
    (sq_nonneg ‖(g (WithLp.toLp 2 (x, y))).fst + (2 * L) • (x - z)‖) hpos hd
  have hs := hw.trans (add_le_add ht le_rfl)
  rw [← add_div, le_div_iff₀ hpos] at hs
  have he := WithLp.prod_norm_sq_eq_of_L2 (regularizedGradient g L z (WithLp.toLp 2 (x, y)))
  change ‖regularizedGradient g L z (WithLp.toLp 2 (x, y))‖ ^ 2 =
    ‖(g (WithLp.toLp 2 (x, y))).fst + (2 * L) • (x - z)‖ ^ 2 +
      ‖(g (WithLp.toLp 2 (x, y))).snd + 0‖ ^ 2 at he
  simp only [add_zero] at he
  have hroot := Real.sq_sqrt hpos.le
  have hrootpos := Real.sqrt_pos.mpr hpos
  rw [le_div_iff₀ hrootpos]
  have hh : (‖x - primal f L z‖ * Real.sqrt (L * μ)) ^ 2 ≤
      ‖regularizedGradient g L z (WithLp.toLp 2 (x, y))‖ ^ 2 := by
    rw [mul_pow, hroot]
    nlinarith
  nlinarith [norm_nonneg (regularizedGradient g L z (WithLp.toLp 2 (x, y))),
    mul_nonneg (norm_nonneg (x - primal f L z)) hrootpos.le]

lemma setup_hessian_dual_nonpos {p : LongTails.Setups.NonconvexPLSecondOrder.Params}
    {f : LongTails.Setups.NonconvexPLSecondOrder.Space p → ℝ} {oracle}
    (hv : LongTails.Setups.NonconvexPLSecondOrder.spec.valid p)
    (hf : LongTails.Setups.NonconvexPLSecondOrder.spec.admissible p f oracle)
    (x : p.E) (y : p.F)
    (hy : ∀ v, f (WithLp.toLp 2 (x, v)) ≤ f (WithLp.toLp 2 (x, y))) (v : p.F) :
    ⟪fderiv ℝ (gradient f) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (0, v)),
      WithLp.toLp 2 (0, v)⟫ ≤ 0 := by
  have H := setup_hyp hv hf
  have hzero := H.max_gradient_zero hy
  obtain ⟨_, _, hρ, _⟩ := hv
  obtain ⟨hg, hdiff, _, hLip, _⟩ := hf
  rw [real_inner_comm]
  apply hessian_nonpos_of_line_max hρ.le hg (fun w => (hdiff w).hasFDerivAt) hLip
  · change ⟪(gradient f (WithLp.toLp 2 (x, y))).fst, 0⟫ +
      ⟪(gradient f (WithLp.toLp 2 (x, y))).snd, v⟫ = 0
    rw [hzero, inner_zero_left, inner_zero_right, add_zero]
  · intro t
    have he : WithLp.toLp 2 (x, y) + t • WithLp.toLp 2 (0, v) = WithLp.toLp 2 (x, y + t • v) := by
      apply WithLp.ofLp_injective 2
      simp
    rw [he]
    exact hy (y + t • v)

lemma setup_hessian_bound {p : LongTails.Setups.NonconvexPLSecondOrder.Params}
    {f : LongTails.Setups.NonconvexPLSecondOrder.Space p → ℝ} {oracle}
    (hv : LongTails.Setups.NonconvexPLSecondOrder.spec.valid p)
    (hf : LongTails.Setups.NonconvexPLSecondOrder.spec.admissible p f oracle)
    (w v : LongTails.Setups.NonconvexPLSecondOrder.Space p) :
    ‖fderiv ℝ (gradient f) w v‖ ≤ p.L * ‖v‖ := by
  have hL : 0 ≤ p.L := (hv.1.trans_le hv.2.1).le
  have hl : LipschitzWith ⟨p.L, hL⟩ (gradient f) :=
    lipschitzWith_iff_norm_sub_le.mpr hf.2.2.1
  have hb : ‖fderiv ℝ (gradient f) w‖ ≤ p.L := norm_fderiv_le_of_lipschitz ℝ hl
  exact (fderiv ℝ (gradient f) w).le_of_opNorm_le hb v

omit [CompleteSpace E] [CompleteSpace F] in
lemma regularizedHessian_inner_energy (H : WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F))
    {L : ℝ} (hs : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫)
    (hbound : ∀ u, ‖H u‖ ≤ L * ‖u‖)
    (hdual : ∀ b : F, ⟪H (WithLp.toLp 2 (0, b)), WithLp.toLp 2 (0, b)⟫ ≤ 0)
    (v : WithLp 2 (E × F)) :
    L * ‖v.fst‖ ^ 2 ≤ ⟪regularizedHessian H L v, WithLp.toLp 2 (v.fst, -v.snd)⟫ := by
  let a : WithLp 2 (E × F) := WithLp.toLp 2 (v.fst, 0)
  let b : WithLp 2 (E × F) := WithLp.toLp 2 (0, v.snd)
  have he : a + b = v := by
    change WithLp.toLp 2 (v.fst, 0) + WithLp.toLp 2 (0, v.snd) = v
    rw [← WithLp.toLp_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
    exact (WithLp.equiv 2 (E × F)).left_inv v
  have hsign : a - b = WithLp.toLp 2 (v.fst, -v.snd) := by
    apply WithLp.ofLp_injective 2
    simp [a, b]
  have hh := primal_component_inner_energy H hs a b
    (by simp [a, b, WithLp.prod_inner_apply]) (hbound a) (hdual v.snd)
  rw [he, hsign] at hh
  simpa only [a, WithLp.norm_toLp_fst, regularizedHessian, add_apply, smul_apply, primalBlock_apply] using hh

omit [CompleteSpace E] [CompleteSpace F] in
lemma regularizedHessian_energy (H : WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F))
    {L : ℝ} (hs : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫)
    (hbound : ∀ u, ‖H u‖ ≤ L * ‖u‖)
    (hdual : ∀ b : F, ⟪H (WithLp.toLp 2 (0, b)), WithLp.toLp 2 (0, b)⟫ ≤ 0)
    (v : WithLp 2 (E × F)) :
    L * ‖v.fst‖ ^ 2 ≤ ‖regularizedHessian H L v‖ * ‖v‖ := by
  have he : ‖WithLp.toLp 2 (v.fst, -v.snd)‖ = ‖v‖ := by
    have h₁ := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (v.fst, -v.snd))
    have h₂ := WithLp.prod_norm_sq_eq_of_L2 v
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, norm_neg] at h₁
    nlinarith [norm_nonneg (WithLp.toLp 2 (v.fst, -v.snd)), norm_nonneg v]
  have hh := (regularizedHessian_inner_energy H hs hbound hdual v).trans
    (real_inner_le_norm (regularizedHessian H L v) (WithLp.toLp 2 (v.fst, -v.snd)))
  rwa [he] at hh

omit [CompleteSpace E] [CompleteSpace F] in
lemma regularizedHessian_symmetric (H : WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F))
    (hs : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫) (L : ℝ) (u v : WithLp 2 (E × F)) :
    ⟪regularizedHessian H L u, v⟫ = ⟪u, regularizedHessian H L v⟫ := by
  simp only [regularizedHessian, add_apply, smul_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, inner_smul_right]
  rw [hs]
  congr 2
  simp [primalBlock_apply, WithLp.prod_inner_apply]

omit [CompleteSpace E] [CompleteSpace F] in
lemma regularizedResponse_primal_bias [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (H : WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F)) {L t : ℝ} (hL : 0 < L) (ht : 0 < t)
    (hs : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫)
    (hbound : ∀ u, ‖H u‖ ≤ L * ‖u‖)
    (hdual : ∀ b : F, ⟪H (WithLp.toLp 2 (0, b)), WithLp.toLp 2 (0, b)⟫ ≤ 0)
    (v : WithLp 2 (E × F)) :
    4 * L ^ 2 * ‖(tikhonovResponse (regularizedHessian H L) t (regularizedHessian H L v) - v).fst‖ ^ 4 ≤
      t * ‖v‖ ^ 4 := by
  let K := regularizedHessian H L
  let d := tikhonovResponse K t (K v) - v
  have hK : ∀ u v, ⟪K u, v⟫ = ⟪u, K v⟫ := regularizedHessian_symmetric H hs L
  have hd : ‖d‖ ≤ ‖v‖ := tikhonovResponse_bias_bound K hK ht v
  have hr : 4 * ‖K d‖ ^ 2 ≤ t * ‖v‖ ^ 2 := tikhonovResponse_bias_residual K hK ht v
  have he : L * ‖d.fst‖ ^ 2 ≤ ‖K d‖ * ‖d‖ := regularizedHessian_energy H hs hbound hdual d
  have he' := pow_le_pow_left₀ (mul_nonneg hL.le (sq_nonneg ‖d.fst‖)) he 2
  have hd' := pow_le_pow_left₀ (norm_nonneg d) hd 2
  have hscaled := mul_le_mul_of_nonneg_left hd' (show 0 ≤ 4 * ‖K d‖ ^ 2 by positivity)
  have hr' := mul_le_mul_of_nonneg_right hr (sq_nonneg ‖v‖)
  change 4 * L ^ 2 * ‖d.fst‖ ^ 4 ≤ t * ‖v‖ ^ 4
  nlinarith

omit [CompleteSpace E] [CompleteSpace F] in
lemma regularizedHessian_norm (H : WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F))
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ u, ‖H u‖ ≤ L * ‖u‖) :
    ‖regularizedHessian H L‖ ≤ 3 * L := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hp : ‖primalBlock v‖ ≤ ‖v‖ := by
    rw [primalBlock_apply, WithLp.norm_toLp_fst]
    exact WithLp.norm_fst_le E v
  change ‖H v + (2 * L) • primalBlock v‖ ≤ 3 * L * ‖v‖
  have hh := norm_add_le (H v) ((2 * L) • primalBlock v)
  rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ 2 * L by positivity)] at hh
  have hb := hbound v
  nlinarith

omit [CompleteSpace E] [CompleteSpace F] in
lemma regularizedHessian_difference (A B : WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F)) (L : ℝ) :
    regularizedHessian A L - regularizedHessian B L = A - B := by
  unfold regularizedHessian
  abel

lemma regularized_root_error [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F → ℝ} {g : WithLp 2 (E × F) → WithLp 2 (E × F)} {L μ : ℝ}
    (H : Hyp f (fun x y => (g (WithLp.toLp 2 (x, y))).fst)
      (fun x y => (g (WithLp.toLp 2 (x, y))).snd) L μ)
    (z : E) (w : WithLp 2 (E × F)) :
    ∃ q, regularizedGradient g L z q = 0 ∧
      (μ / 8) * ‖q - w‖ ≤ ‖regularizedGradient g L z w‖ := by
  obtain ⟨v, hv, hd⟩ := H.saddle_residual_bound z w.fst w.snd
  let q : WithLp 2 (E × F) := WithLp.toLp 2 (primal f L z, v)
  refine ⟨q, regularizedGradient_root H z v hv, ?_⟩
  have hw : WithLp.toLp 2 (w.fst, w.snd) = w := (WithLp.equiv 2 (E × F)).left_inv w
  rw [hw] at hd
  have he := WithLp.prod_norm_sq_eq_of_L2 (q - w)
  change ‖q - w‖ ^ 2 = ‖primal f L z - w.fst‖ ^ 2 + ‖v - w.snd‖ ^ 2 at he
  rw [norm_sub_rev (primal f L z) w.fst, norm_sub_rev v w.snd] at he
  have hr := WithLp.prod_norm_sq_eq_of_L2 (regularizedGradient g L z w)
  simp only [regularizedGradient, WithLp.add_fst, WithLp.add_snd,
    WithLp.toLp_fst, WithLp.toLp_snd, add_zero] at hr
  change ‖regularizedGradient g L z w‖ ^ 2 = _ at hr
  rw [← he, ← hr] at hd
  have hn : 0 ≤ μ * ‖q - w‖ := mul_nonneg H.hμ.le (norm_nonneg _)
  nlinarith [norm_nonneg (regularizedGradient g L z w),
    sq_nonneg (μ * ‖q - w‖ - 8 * ‖regularizedGradient g L z w‖)]

lemma regularized_zero_saddle [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F → ℝ} {g : WithLp 2 (E × F) → WithLp 2 (E × F)} {L μ : ℝ}
    (H : Hyp f (fun x y => (g (WithLp.toLp 2 (x, y))).fst)
      (fun x y => (g (WithLp.toLp 2 (x, y))).snd) L μ)
    (z : E) (w : WithLp 2 (E × F)) (hw : regularizedGradient g L z w = 0) :
    w.fst = primal f L z ∧ ∀ y, f (primal f L z) y ≤ f (primal f L z) w.snd := by
  have he : WithLp.toLp 2 (w.fst, w.snd) = w := (WithLp.equiv 2 (E × F)).left_inv w
  have hp := regularized_primal_error H z w.fst w.snd
  rw [he, hw, norm_zero, zero_div] at hp
  have hx : w.fst = primal f L z := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hp (norm_nonneg _)))
  have hy : (g w).snd = 0 := by
    have hh := congrArg WithLp.snd hw
    simpa only [regularizedGradient, WithLp.add_snd, WithLp.toLp_snd, add_zero, WithLp.zero_snd] using hh
  refine ⟨hx, fun y => ?_⟩
  have hh := H.ply w.fst w.snd y
  rw [he, hy, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hh
  rw [← hx]
  nlinarith [H.hμ]

omit [CompleteSpace E] [CompleteSpace F] in
lemma regularizedGradient_residual_taylor
    {g : WithLp 2 (E × F) → WithLp 2 (E × F)}
    {H : WithLp 2 (E × F) → WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F)} {ρ : ℝ}
    (hg : ∀ w, HasFDerivAt g (H w) w)
    (hH : ∀ w v, ‖H w - H v‖ ≤ ρ * ‖w - v‖)
    (L : ℝ) (z : E) (w d : WithLp 2 (E × F)) :
    ‖regularizedGradient g L z (w + d) -
      (regularizedGradient g L z w + regularizedHessian (H w) L d)‖ ≤ ρ / 2 * ‖d‖ ^ 2 := by
  have he : regularizedGradient g L z (w + d) -
      (regularizedGradient g L z w + regularizedHessian (H w) L d) =
      g (w + d) - g w - H w d := by
    simp only [regularizedGradient, regularizedHessian, add_apply, smul_apply, primalBlock_apply]
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> simp [smul_add, smul_sub] <;> abel
  rw [he]
  have hh := LongTails.Proofs.CubicRegularization.gradient_taylor hg hH w d
  convert hh using 1
  ring

end OracleTemplate.PLMinimax
