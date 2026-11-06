import LongTails.Algorithms.ConstrainedSaddleCubic
import LongTails.Proofs.ConstrainedMinimaxEnvelope

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ConstrainedSaddleModel

open LongTails.Algorithms.ConstrainedSaddleCubic
open LongTails.Setups.ConstrainedMinimaxSecondOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma model_hasGradient (w : E) (c : ℝ) (g : E) (A : E →L[ℝ] E)
    (hs : ∀ a b, ⟪a, A b⟫ = ⟪A a, b⟫) (v : E) :
    HasGradientAt (quadraticModel w c g A) (g + A (v - w)) v := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd := (hasFDerivAt_id (𝕜 := ℝ) v).sub_const w
  have hl := (hasFDerivAt_const g v).inner ℝ hd
  have hq := (hd.inner ℝ (A.hasFDerivAt.comp v hd)).mul_const (1 / 2 : ℝ)
  convert (hl.const_add c).add hq using 1
  · funext x
    simp [quadraticModel, div_eq_mul_inv]
  · ext u
    simp [InnerProductSpace.toDual_apply_apply, hs, real_inner_comm u]
    ring_nf
    simp [inner_sub_right, hs]

lemma model_gradient_derivative (w : E) (c : ℝ) (g : E) (A : E →L[ℝ] E)
    (hs : ∀ a b, ⟪a, A b⟫ = ⟪A a, b⟫) (v : E) :
    HasFDerivAt (gradient (quadraticModel w c g A)) A v := by
  have he : gradient (quadraticModel w c g A) = fun x => g + A (x - w) := by
    funext x
    exact (model_hasGradient w c g A hs x).gradient
  rw [he]
  convert (A.hasFDerivAt.comp v ((hasFDerivAt_id v).sub_const w)).const_add g using 1 <;> simp

omit [CompleteSpace E] in
lemma model_expansion (w : E) (c : ℝ) (g : E) (A : E →L[ℝ] E)
    (hs : ∀ a b, ⟪a, A b⟫ = ⟪A a, b⟫) (u v : E) :
    quadraticModel w c g A v = quadraticModel w c g A u +
      ⟪g + A (u - w), v - u⟫ + ⟪v - u, A (v - u)⟫ / 2 := by
  have he : v - w = (u - w) + (v - u) := by abel
  unfold quadraticModel
  rw [he]
  simp only [map_add, inner_add_left, inner_add_right]
  rw [hs (u - w) (v - u), real_inner_comm (A (u - w)) (v - u)]
  ring

lemma hessian_symmetric {p : Params} {f : Space p → ℝ} (H : Regularity p f) (w : Space p) :
    ∀ a b, ⟪a, fderiv ℝ (gradient f) w b⟫ = ⟪fderiv ℝ (gradient f) w a, b⟫ := by
  have hs := OracleTemplate.SpectralGradient.hessian_symmetric
    (fun v => (H.hasGradient v).differentiableAt) H.gradient_differentiable w
  exact fun a b => (hs a b).symm

lemma model_value_error {p : Params} {f : Space p → ℝ} (H : Regularity p f) (w v : Space p) :
    |f v - quadraticModel w (f w) (gradient f w) (fderiv ℝ (gradient f) w) v| ≤
      p.ρ * ‖v - w‖ ^ 3 / 6 := by
  have ht := CubicRegularization.objective_taylor (fun x => (H.hasGradient x).hasFDerivAt)
    (fun x => (H.gradient_differentiable x).hasFDerivAt) H.hessian_lipschitz w (v - w)
  simp only [add_sub_cancel] at ht
  convert ht using 1
  unfold quadraticModel
  congr 1
  ring

lemma model_gradient_error {p : Params} {f : Space p → ℝ} (H : Regularity p f) (w v : Space p) :
    ‖gradient f v - gradient (quadraticModel w (f w) (gradient f w)
      (fderiv ℝ (gradient f) w)) v‖ ≤ p.ρ * ‖v - w‖ ^ 2 / 2 := by
  rw [(model_hasGradient w (f w) (gradient f w) (fderiv ℝ (gradient f) w)
    (hessian_symmetric H w) v).gradient]
  have ht := CubicRegularization.gradient_taylor
    (fun x => (H.gradient_differentiable x).hasFDerivAt) H.hessian_lipschitz w (v - w)
  simpa only [add_sub_cancel, sub_add_eq_sub_sub] using ht

lemma hessian_dual_bound {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (w : Space p) (b : p.F) :
    ⟪WithLp.toLp 2 (0, b), fderiv ℝ (gradient f) w (WithLp.toLp 2 (0, b))⟫ ≤ -p.μ * ‖b‖ ^ 2 := by
  let d : Space p := WithLp.toLp 2 (0, b)
  let a := ⟪d, fderiv ℝ (gradient f) w d⟫ + p.μ * ‖b‖ ^ 2
  by_contra hh
  have ha : 0 < a := by
    change ¬⟪d, fderiv ℝ (gradient f) w d⟫ ≤ -p.μ * ‖b‖ ^ 2 at hh
    change 0 < ⟪d, fderiv ℝ (gradient f) w d⟫ + p.μ * ‖b‖ ^ 2
    linarith
  let c := p.ρ * ‖d‖ ^ 3 + 1
  have hρ : 0 < p.ρ := hv.2.2.1
  have hc : 0 < c := by dsimp [c]; positivity
  let t := a / c
  have ht : 0 < t := div_pos ha hc
  have htc : t * c = a := div_mul_cancel₀ _ hc.ne'
  have hTaylor := CubicRegularization.objective_taylor (fun x => (H.hasGradient x).hasFDerivAt)
    (fun x => (H.gradient_differentiable x).hasFDerivAt) H.hessian_lipschitz w (t • d)
  simp only [inner_smul_right, map_smul, real_inner_smul_left, norm_smul,
    Real.norm_of_nonneg ht.le] at hTaylor
  have hlow := (abs_le.mp hTaylor).1
  have hsc := H.strongly_concave w.fst w.snd (w.snd + t • b)
  have he : WithLp.toLp 2 (w.fst, w.snd + t • b) = w + t • d := by
    apply (WithLp.equiv 2 (p.E × p.F)).injective
    ext <;> simp [d]
  have he0 : WithLp.toLp 2 (w.fst, w.snd) = w := rfl
  rw [he, he0] at hsc
  simp only [add_sub_cancel_left, inner_smul_right, norm_smul, Real.norm_of_nonneg ht.le] at hsc
  have hi : ⟪gradient f w, d⟫ = ⟪(gradient f w).snd, b⟫ := by
    change ⟪(gradient f w).fst, (0 : p.E)⟫ + ⟪(gradient f w).snd, b⟫ = _
    simp only [inner_zero_right, zero_add]
  rw [hi] at hlow
  have hineq : a ≤ p.ρ * ‖d‖ ^ 3 * t / 3 := by
    apply le_of_mul_le_mul_left (a := t ^ 2) _ (sq_pos_of_pos ht)
    change t ^ 2 * (⟪d, fderiv ℝ (gradient f) w d⟫ + p.μ * ‖b‖ ^ 2) ≤ _
    nlinarith
  dsimp [c] at htc
  nlinarith

lemma model_regularity {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (w : Space p) :
    Regularity p (quadraticModel w (f w) (gradient f w) (fderiv ℝ (gradient f) w)) := by
  let A := fderiv ℝ (gradient f) w
  let q := quadraticModel w (f w) (gradient f w) A
  have hs := hessian_symmetric H w
  have hg (v : Space p) : gradient q v = gradient f w + A (v - w) :=
    (model_hasGradient w (f w) (gradient f w) A hs v).gradient
  have hA : ‖A‖ ≤ p.L := norm_fderiv_le_of_lip' ℝ (hv.1.trans_le hv.2.1).le
    (Filter.Eventually.of_forall (fun v => H.gradient_lipschitz v w))
  have hd (v : Space p) : HasFDerivAt (gradient q) A v :=
    model_gradient_derivative w (f w) (gradient f w) A hs v
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v
    change HasGradientAt q (gradient q v) v
    rw [hg]
    exact model_hasGradient w (f w) (gradient f w) A hs v
  · exact fun v => (hd v).differentiableAt
  · intro u v
    change ‖gradient q u - gradient q v‖ ≤ _
    rw [hg, hg]
    have he : gradient f w + A (u - w) - (gradient f w + A (v - w)) = A (u - v) := by
      rw [map_sub, map_sub, map_sub]
      abel
    rw [he]
    exact (A.le_opNorm (u - v)).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  · intro u v
    change ‖fderiv ℝ (gradient q) u - fderiv ℝ (gradient q) v‖ ≤ _
    rw [(hd u).fderiv, (hd v).fderiv]
    rw [sub_self, ContinuousLinearMap.opNorm_zero]
    exact mul_nonneg hv.2.2.1.le (norm_nonneg (u - v))
  · intro x y y'
    change q (WithLp.toLp 2 (x, y')) ≤ q (WithLp.toLp 2 (x, y)) +
      ⟪(gradient q (WithLp.toLp 2 (x, y))).snd, y' - y⟫ - p.μ / 2 * ‖y' - y‖ ^ 2
    have he := model_expansion w (f w) (gradient f w) A hs
      (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (x, y'))
    change q _ = q _ + _ + _ at he
    rw [← hg] at he
    have hsub : WithLp.toLp 2 (x, y') - WithLp.toLp 2 (x, y) =
        WithLp.toLp 2 (0, y' - y) := by rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self]
    rw [hsub] at he
    have hi : ⟪gradient q (WithLp.toLp 2 (x, y)), WithLp.toLp 2 (0, y' - y)⟫ =
        ⟪(gradient q (WithLp.toLp 2 (x, y))).snd, y' - y⟫ := by
      change ⟪(gradient q (WithLp.toLp 2 (x, y))).fst, (0 : p.E)⟫ +
        ⟪(gradient q (WithLp.toLp 2 (x, y))).snd, y' - y⟫ = _
      simp only [inner_zero_right, zero_add]
    rw [hi] at he
    have hb := hessian_dual_bound H hv w (y' - y)
    change ⟪WithLp.toLp 2 (0, y' - y), A (WithLp.toLp 2 (0, y' - y))⟫ ≤ _ at hb
    linarith

open ConstrainedMinimaxEnvelope

lemma model_anchor {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) :
    let w := WithLp.toLp 2 (primal f z, dual f z)
    let q := quadraticModel w (f w) (gradient f w) (fderiv ℝ (gradient f) w)
    primal q z = primal f z ∧ dual q z = dual f z := by
  dsimp only
  let w := WithLp.toLp 2 (primal f z, dual f z)
  let q := quadraticModel w (f w) (gradient f w) (fderiv ℝ (gradient f) w)
  change primal q z = primal f z ∧ dual q z = dual f z
  have hq := model_regularity H hv w
  have hg : gradient q w = gradient f w := by
    rw [(model_hasGradient w (f w) (gradient f w) (fderiv ℝ (gradient f) w)
      (hessian_symmetric H w) w).gradient]
    simp only [sub_self, map_zero, add_zero]
  apply saddle_identify hq hv z (primal f z) (dual f z) (dual_spec H hv z).1
  · change (gradient q w).fst + _ = 0
    rw [hg]
    exact saddle_primal_zero H hv z
  · change ∀ y ∈ p.Y, ⟪(gradient q w).snd, y - dual f z⟫ ≤ 0
    rw [hg]
    exact saddle_dual_normal H hv z

lemma mixed_center_distance {p : Params} {f q : Space p → ℝ}
    (H : Regularity p f) (Q : Regularity p q) (hv : spec.valid p) (z z0 : p.E) :
    ‖WithLp.toLp 2 (primal f z, dual q z) - WithLp.toLp 2 (primal f z0, dual q z0)‖ ≤
      Real.sqrt (4 + p.L / p.μ) * ‖z - z0‖ := by
  have hx := primal_center_distance_sq H hv z z0
  have hy := dual_center_distance_sq Q hv z z0
  have hn := WithLp.prod_norm_sq_eq_of_L2
    (WithLp.toLp 2 (primal f z, dual q z) - WithLp.toLp 2 (primal f z0, dual q z0))
  change ‖WithLp.toLp 2 (primal f z, dual q z) - WithLp.toLp 2 (primal f z0, dual q z0)‖ ^ 2 =
    ‖primal f z - primal f z0‖ ^ 2 + ‖dual q z - dual q z0‖ ^ 2 at hn
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hμ : 0 < p.μ := hv.1
  have hs := Real.sq_sqrt (show 0 ≤ 4 + p.L / p.μ by positivity)
  have hp := mul_nonneg (Real.sqrt_nonneg (4 + p.L / p.μ)) (norm_nonneg (z - z0))
  nlinarith [norm_nonneg (WithLp.toLp 2 (primal f z, dual q z) -
    WithLp.toLp 2 (primal f z0, dual q z0)), sq_nonneg (Real.sqrt (4 + p.L / p.μ) * ‖z - z0‖ -
      ‖WithLp.toLp 2 (primal f z, dual q z) - WithLp.toLp 2 (primal f z0, dual q z0)‖)]

lemma model_envelope_value_error {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z0 z : p.E) :
    let w := WithLp.toLp 2 (primal f z0, dual f z0)
    let q := quadraticModel w (f w) (gradient f w) (fderiv ℝ (gradient f) w)
    |envelope f z - envelope q z| ≤
      p.ρ * Real.sqrt (4 + p.L / p.μ) ^ 3 * ‖z - z0‖ ^ 3 / 6 := by
  dsimp only
  let w := WithLp.toLp 2 (primal f z0, dual f z0)
  let q := quadraticModel w (f w) (gradient f w) (fderiv ℝ (gradient f) w)
  change |envelope f z - envelope q z| ≤ _
  have Q := model_regularity H hv w
  have ha := model_anchor H hv z0
  change primal q z0 = primal f z0 ∧ dual q z0 = dual f z0 at ha
  have h1 := mixed_center_distance Q H hv z z0
  have h2 := mixed_center_distance H Q hv z z0
  rw [ha.1] at h1
  rw [ha.2] at h2
  have bound (v : Space p) (hd : ‖v - w‖ ≤ Real.sqrt (4 + p.L / p.μ) * ‖z - z0‖) :
      |f v - q v| ≤ p.ρ * Real.sqrt (4 + p.L / p.μ) ^ 3 * ‖z - z0‖ ^ 3 / 6 := by
    have ht := model_value_error H w v
    change |f v - q v| ≤ _ at ht
    calc
      |f v - q v| ≤ p.ρ * ‖v - w‖ ^ 3 / 6 := ht
      _ ≤ p.ρ * (Real.sqrt (4 + p.L / p.μ) * ‖z - z0‖) ^ 3 / 6 := by
        gcongr
        exact hv.2.2.1.le
      _ = _ := by ring
  exact envelope_value_comparison H Q hv z (bound _ h1) (bound _ h2)

lemma model_envelope_gradient_error_sq {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z0 z : p.E) :
    let w := WithLp.toLp 2 (primal f z0, dual f z0)
    let q := quadraticModel w (f w) (gradient f w) (fderiv ℝ (gradient f) w)
    ‖gradient (envelope f) z - gradient (envelope q) z‖ ^ 2 ≤
      p.ρ ^ 2 * (4 + p.L / p.μ) ^ 3 * ‖z - z0‖ ^ 4 := by
  dsimp only
  let w := WithLp.toLp 2 (primal f z0, dual f z0)
  let q := quadraticModel w (f w) (gradient f w) (fderiv ℝ (gradient f) w)
  let v := WithLp.toLp 2 (primal q z, dual q z)
  change ‖gradient (envelope f) z - gradient (envelope q) z‖ ^ 2 ≤ _
  have Q := model_regularity H hv w
  have ha := model_anchor H hv z0
  change primal q z0 = primal f z0 ∧ dual q z0 = dual f z0 at ha
  have hd := saddle_center_distance_sq Q hv z z0
  rw [ha.1, ha.2] at hd
  have hn := WithLp.prod_norm_sq_eq_of_L2 (v - w)
  have hd' : ‖v - w‖ ^ 2 ≤ (4 + p.L / p.μ) * ‖z - z0‖ ^ 2 := by
    rw [hn]
    exact hd
  have hr := model_gradient_error H w v
  change ‖gradient f v - gradient q v‖ ≤ _ at hr
  have hρ : 0 < p.ρ := hv.2.2.1
  have hμ : 0 < p.μ := hv.1
  have hL : 0 < p.L := hμ.trans_le hv.2.1
  have hs : 0 ≤ 4 + p.L / p.μ := by positivity
  have hb : ‖gradient f v - gradient q v‖ ≤
      p.ρ * (4 + p.L / p.μ) * ‖z - z0‖ ^ 2 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hd' hρ.le]
  have hbs := (sq_le_sq₀ (norm_nonneg (gradient f v - gradient q v))
    (show 0 ≤ p.ρ * (4 + p.L / p.μ) * ‖z - z0‖ ^ 2 / 2 by positivity)).mpr hb
  have hp := envelope_gradient_perturbation_sq H Q hv z
  change ‖gradient (envelope f) z - gradient (envelope q) z‖ ^ 2 ≤
    4 * (p.L / p.μ) * ‖gradient f v - gradient q v‖ ^ 2 at hp
  calc
    _ ≤ 4 * (p.L / p.μ) * ‖gradient f v - gradient q v‖ ^ 2 := hp
    _ ≤ 4 * (p.L / p.μ) * (p.ρ * (4 + p.L / p.μ) * ‖z - z0‖ ^ 2 / 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hbs (by positivity)
    _ = p.ρ ^ 2 * (p.L / p.μ) * (4 + p.L / p.μ) ^ 2 * ‖z - z0‖ ^ 4 := by ring
    _ ≤ p.ρ ^ 2 * (4 + p.L / p.μ) * (4 + p.L / p.μ) ^ 2 * ‖z - z0‖ ^ 4 := by
      gcongr
      linarith
    _ = _ := by ring

lemma model_envelope_gradient_error {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z0 z : p.E) :
    let w := WithLp.toLp 2 (primal f z0, dual f z0)
    let q := quadraticModel w (f w) (gradient f w) (fderiv ℝ (gradient f) w)
    ‖gradient (envelope f) z - gradient (envelope q) z‖ ≤
      p.ρ * Real.sqrt (4 + p.L / p.μ) ^ 3 * ‖z - z0‖ ^ 2 := by
  dsimp only
  have hh := model_envelope_gradient_error_sq H hv z0 z
  dsimp only at hh
  have hρ : 0 < p.ρ := hv.2.2.1
  have hμ : 0 < p.μ := hv.1
  have hL : 0 < p.L := hμ.trans_le hv.2.1
  have hs : 0 ≤ 4 + p.L / p.μ := by positivity
  have hpow : Real.sqrt (4 + p.L / p.μ) ^ 6 = (4 + p.L / p.μ) ^ 3 := by
    calc
      _ = (Real.sqrt (4 + p.L / p.μ) ^ 2) ^ 3 := by ring
      _ = _ := by rw [Real.sq_sqrt hs]
  have he : (p.ρ * Real.sqrt (4 + p.L / p.μ) ^ 3 * ‖z - z0‖ ^ 2) ^ 2 =
      p.ρ ^ 2 * (4 + p.L / p.μ) ^ 3 * ‖z - z0‖ ^ 4 := by
    simp only [mul_pow, ← pow_mul]
    norm_num only at *
    rw [hpow]
  have hp : 0 ≤ p.ρ * Real.sqrt (4 + p.L / p.μ) ^ 3 * ‖z - z0‖ ^ 2 := by positivity
  nlinarith

end LongTails.Proofs.ConstrainedSaddleModel
