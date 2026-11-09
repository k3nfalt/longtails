import LongTails.Proofs.ConstrainedSaddleModel

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ConstrainedSaddlePerturbation

open LongTails.Setups.ConstrainedMinimaxSecondOrder
open LongTails.Algorithms.ConstrainedSaddleCubic
open ConstrainedMinimaxEnvelope

noncomputable def tilt {p : Params} (f : Space p → ℝ) (w e v : Space p) : ℝ :=
  f v - ⟪e, v - w⟫

lemma tilt_hasGradient {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (w e v : Space p) : HasGradientAt (tilt f w e) (gradient f v - e) v := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hl := (hasFDerivAt_const e v).inner ℝ ((hasFDerivAt_id v).sub_const w)
  convert (H.hasGradient v).hasFDerivAt.sub hl using 1
  · rfl
  · ext u
    simp [InnerProductSpace.toDual_apply_apply]

lemma tilt_gradient {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (w e v : Space p) : gradient (tilt f w e) v = gradient f v - e :=
  (tilt_hasGradient H w e v).gradient

lemma tilt_gradient_derivative {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (w e v : Space p) :
    HasFDerivAt (gradient (tilt f w e)) (fderiv ℝ (gradient f) v) v := by
  have he : gradient (tilt f w e) = fun x => gradient f x - e := by
    funext x
    exact tilt_gradient H w e x
  rw [he]
  exact (H.gradient_differentiable v).hasFDerivAt.sub_const e

lemma tilt_regularity {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (w e : Space p) : Regularity p (tilt f w e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v
    rw [tilt_gradient H]
    exact tilt_hasGradient H w e v
  · exact fun v => (tilt_gradient_derivative H w e v).differentiableAt
  · intro u v
    rw [tilt_gradient H, tilt_gradient H, sub_sub_sub_cancel_right]
    exact H.gradient_lipschitz u v
  · intro u v
    rw [(tilt_gradient_derivative H w e u).fderiv, (tilt_gradient_derivative H w e v).fderiv]
    exact H.hessian_lipschitz u v
  · intro x y y'
    have hc := H.strongly_concave x y y'
    rw [tilt_gradient H]
    unfold tilt
    change f (WithLp.toLp 2 (x, y')) -
        (⟪e.fst, x - w.fst⟫ + ⟪e.snd, y' - w.snd⟫) ≤
      f (WithLp.toLp 2 (x, y)) - (⟪e.fst, x - w.fst⟫ + ⟪e.snd, y - w.snd⟫) +
        ⟪(gradient f (WithLp.toLp 2 (x, y))).snd - e.snd, y' - y⟫ - p.μ / 2 * ‖y' - y‖ ^ 2
    simp only [inner_sub_left, inner_sub_right] at hc ⊢
    linarith

lemma tilt_saddle {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (w e : Space p) (hw : w.snd ∈ p.Y)
    (hx : (gradient f w).fst + (2 * p.L) • (w.fst - z) = e.fst)
    (hy : ∀ y ∈ p.Y, ⟪(gradient f w).snd - e.snd, y - w.snd⟫ ≤ 0) :
    primal (tilt f w e) z = w.fst ∧ dual (tilt f w e) z = w.snd := by
  apply saddle_identify (tilt_regularity H w e) hv z w.fst w.snd hw
  · rw [tilt_gradient H]
    change (gradient f w).fst - e.fst + (2 * p.L) • (w.fst - z) = 0
    rw [← hx]
    abel
  · rw [tilt_gradient H]
    exact hy

lemma tilt_envelope_gradient_sq {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (w e : Space p) (z : p.E) :
    ‖gradient (envelope f) z - gradient (envelope (tilt f w e)) z‖ ^ 2 ≤
      4 * (p.L / p.μ) * ‖e‖ ^ 2 := by
  have hh := envelope_gradient_perturbation_sq H (tilt_regularity H w e) hv z
  rw [tilt_gradient H] at hh
  simpa only [sub_sub_cancel] using hh

lemma tilt_envelope_gradient {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (w e : Space p) (z : p.E) :
    ‖gradient (envelope f) z - gradient (envelope (tilt f w e)) z‖ ≤
      2 * Real.sqrt (p.L / p.μ) * ‖e‖ := by
  have hh := tilt_envelope_gradient_sq H hv w e z
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hμ : 0 < p.μ := hv.1
  have hs := Real.sq_sqrt (show 0 ≤ p.L / p.μ by positivity)
  have hp : 0 ≤ 2 * Real.sqrt (p.L / p.μ) * ‖e‖ := by positivity
  nlinarith

lemma tilt_envelope_increment {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (w e : Space p) (z z' : p.E) :
    |(envelope f z' - envelope (tilt f w e) z') -
      (envelope f z - envelope (tilt f w e) z)| ≤
        2 * Real.sqrt (p.L / p.μ) * ‖e‖ * ‖z' - z‖ := by
  let D := fun x => envelope f x - envelope (tilt f w e) x
  let G := fun x => gradient (envelope f) x - gradient (envelope (tilt f w e)) x
  have hd (x : p.E) : HasFDerivAt D ((InnerProductSpace.toDual ℝ p.E) (G x)) x := by
    have h1 := envelope_hasGradient H hv x
    have h2 := envelope_hasGradient (tilt_regularity H w e) hv x
    rw [← h1.gradient] at h1
    rw [← h2.gradient] at h2
    convert h1.hasFDerivAt.sub h2.hasFDerivAt using 1
    exact (InnerProductSpace.toDual ℝ p.E).map_sub _ _
  have hb (x : p.E) : ‖(InnerProductSpace.toDual ℝ p.E) (G x)‖ ≤
      2 * Real.sqrt (p.L / p.μ) * ‖e‖ := by
    rw [(InnerProductSpace.toDual ℝ p.E).norm_map]
    exact tilt_envelope_gradient H hv w e x
  have hh := (convex_univ : Convex ℝ (Set.univ : Set p.E)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hd x).hasFDerivWithinAt) (fun x _ => hb x) (Set.mem_univ z) (Set.mem_univ z')
  simpa only [D, Real.norm_eq_abs] using hh

lemma tilt_jet {p : Params} {f : Space p → ℝ} (H : Regularity p f) (w e : Space p) :
    LongTails.Algorithms.ConstrainedSaddleCubic.quadraticModel w ((tilt f w e) w)
      (gradient (tilt f w e) w) (fderiv ℝ (gradient (tilt f w e)) w) =
    LongTails.Algorithms.ConstrainedSaddleCubic.quadraticModel w (f w)
      (gradient f w - e) (fderiv ℝ (gradient f) w) := by
  rw [tilt_gradient H, (tilt_gradient_derivative H w e w).fderiv]
  simp [tilt]

lemma corrected_model_errors {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z0 z : p.E) (w e : Space p) (hw : w.snd ∈ p.Y)
    (hx : (gradient f w).fst + (2 * p.L) • (w.fst - z0) = e.fst)
    (hy : ∀ y ∈ p.Y, ⟪(gradient f w).snd - e.snd, y - w.snd⟫ ≤ 0) :
    let q := quadraticModel w (f w) (gradient f w - e) (fderiv ℝ (gradient f) w)
    let R := p.ρ * Real.sqrt (4 + p.L / p.μ) ^ 3
    |(envelope f z - envelope f z0) - (envelope q z - envelope q z0)| ≤
        R * ‖z - z0‖ ^ 3 / 6 + 2 * Real.sqrt (p.L / p.μ) * ‖e‖ * ‖z - z0‖ ∧
      ‖gradient (envelope f) z - gradient (envelope q) z‖ ≤
        R * ‖z - z0‖ ^ 2 + 2 * Real.sqrt (p.L / p.μ) * ‖e‖ := by
  dsimp only
  let q := quadraticModel w (f w) (gradient f w - e) (fderiv ℝ (gradient f) w)
  let T := tilt f w e
  have hT : Regularity p T := tilt_regularity H w e
  have ha := tilt_saddle H hv z0 w e hw hx hy
  have hanchor : WithLp.toLp 2 (primal T z0, dual T z0) = w := by
    rw [ha.1, ha.2]
    rfl
  have hmval (v : p.E) : |envelope T v - envelope q v| ≤
      p.ρ * Real.sqrt (4 + p.L / p.μ) ^ 3 * ‖v - z0‖ ^ 3 / 6 := by
    have hh := ConstrainedSaddleModel.model_envelope_value_error hT hv z0 v
    dsimp only at hh
    rw [hanchor, tilt_jet H] at hh
    exact hh
  have hmgrad : ‖gradient (envelope T) z - gradient (envelope q) z‖ ≤
      p.ρ * Real.sqrt (4 + p.L / p.μ) ^ 3 * ‖z - z0‖ ^ 2 := by
    have hh := ConstrainedSaddleModel.model_envelope_gradient_error hT hv z0 z
    dsimp only at hh
    rw [hanchor, tilt_jet H] at hh
    exact hh
  have heq : envelope T z0 = envelope q z0 := by
    have hh := hmval z0
    simp only [sub_self, norm_zero, zero_pow (by decide : 3 ≠ 0), mul_zero, zero_div] at hh
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)
  constructor
  · have hi := tilt_envelope_increment H hv w e z0 z
    change |(envelope f z - envelope T z) - (envelope f z0 - envelope T z0)| ≤ _ at hi
    rw [heq] at hi
    have hm := hmval z
    rw [abs_le] at hi hm ⊢
    constructor <;> linarith [hi.1, hi.2, hm.1, hm.2]
  · have ht := norm_sub_le_norm_sub_add_norm_sub (gradient (envelope f) z) (gradient (envelope T) z)
      (gradient (envelope q) z)
    have he := tilt_envelope_gradient H hv w e z
    change ‖gradient (envelope f) z - gradient (envelope T) z‖ ≤ _ at he
    linarith

lemma affine_saddle_exists {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (w : Space p) :
    ∃ v, AffineSaddle z w (gradient f w) (fderiv ℝ (gradient f) w) v := by
  let q := quadraticModel w (f w) (gradient f w) (fderiv ℝ (gradient f) w)
  have Q : Regularity p q := ConstrainedSaddleModel.model_regularity H hv w
  have hg (v : Space p) : gradient q v =
      gradient f w + fderiv ℝ (gradient f) w (v - w) :=
    (ConstrainedSaddleModel.model_hasGradient _ _ _ _
      (ConstrainedSaddleModel.hessian_symmetric H w) v).gradient
  refine ⟨WithLp.toLp 2 (primal q z, dual q z), (dual_spec Q hv z).1, ?_, ?_⟩
  · simpa only [hg, WithLp.toLp_fst, WithLp.toLp_snd] using saddle_primal_zero Q hv z
  · intro y hy
    simpa only [hg, WithLp.toLp_fst, WithLp.toLp_snd] using saddle_dual_normal Q hv z y hy

lemma affine_step_spec {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (w : Space p) :
    AffineSaddle z w (gradient f w) (fderiv ℝ (gradient f) w)
      (affineStep z w (gradient f w) (fderiv ℝ (gradient f) w)) := by
  classical
  unfold affineStep
  rw [dite_eq_left (affine_saddle_exists H hv z w)]
  exact (affine_saddle_exists H hv z w).choose_spec

lemma correction_bound {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (w v : Space p) :
    ‖correction w (gradient f w) (fderiv ℝ (gradient f) w) v (gradient f v)‖ ≤
      p.ρ * ‖v - w‖ ^ 2 / 2 := by
  have he := ConstrainedSaddleModel.model_gradient_error H w v
  rw [(ConstrainedSaddleModel.model_hasGradient _ _ _ _
    (ConstrainedSaddleModel.hessian_symmetric H w) v).gradient] at he
  exact he

lemma correction_saddle {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (w g : Space p) (A : Space p →L[ℝ] Space p)
    (v : Space p) (hs : AffineSaddle z w g A v) :
    let e := correction w g A v (gradient f v)
    primal (tilt f v e) z = v.fst ∧ dual (tilt f v e) z = v.snd := by
  dsimp only
  apply tilt_saddle H hv z v _ hs.1
  · change (gradient f v).fst + (2 * p.L) • (v.fst - z) =
      (gradient f v).fst - (g + A (v - w)).fst
    have hz := hs.2.1
    rw [add_eq_zero_iff_eq_neg] at hz
    rw [hz]
    module
  · intro y hy
    change ⟪(gradient f v).snd - ((gradient f v).snd - (g + A (v - w)).snd),
      y - v.snd⟫ ≤ 0
    simpa only [sub_sub_cancel] using hs.2.2 y hy

lemma affine_saddle_identify {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (w v : Space p)
    (hs : AffineSaddle z w (gradient f w) (fderiv ℝ (gradient f) w) v) :
    let q := quadraticModel w (f w) (gradient f w) (fderiv ℝ (gradient f) w)
    primal q z = v.fst ∧ dual q z = v.snd := by
  dsimp only
  have hη : WithLp.toLp 2 (v.fst, v.snd) = v := rfl
  apply saddle_identify (ConstrainedSaddleModel.model_regularity H hv w) hv z v.fst v.snd hs.1
  · rw [(ConstrainedSaddleModel.model_hasGradient _ _ _ _
      (ConstrainedSaddleModel.hessian_symmetric H w) _).gradient]
    simpa only [hη] using hs.2.1
  · intro y hy
    rw [(ConstrainedSaddleModel.model_hasGradient _ _ _ _
      (ConstrainedSaddleModel.hessian_symmetric H w) _).gradient]
    simpa only [hη] using hs.2.2 y hy

lemma affine_step_quadratic_error {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (w : Space p) :
    let v := affineStep z w (gradient f w) (fderiv ℝ (gradient f) w)
    let s := WithLp.toLp 2 (primal f z, dual f z)
    p.μ * ‖v - s‖ ≤ p.ρ * ‖w - s‖ ^ 2 / 2 := by
  let v := affineStep z w (gradient f w) (fderiv ℝ (gradient f) w)
  let q := quadraticModel w (f w) (gradient f w) (fderiv ℝ (gradient f) w)
  let s := WithLp.toLp 2 (primal f z, dual f z)
  have Q : Regularity p q := ConstrainedSaddleModel.model_regularity H hv w
  have he := affine_saddle_identify H hv z w v (affine_step_spec H hv z w)
  have hp := saddle_perturbation_norm Q H hv z
  have ht := ConstrainedSaddleModel.model_gradient_error H w s
  change p.μ * ‖WithLp.toLp 2 (primal q z - primal f z, dual q z - dual f z)‖ ≤
    ‖gradient q s - gradient f s‖ at hp
  rw [he.1, he.2] at hp
  have hd : WithLp.toLp 2 (v.fst - primal f z, v.snd - dual f z) = v - s := by
    rfl
  rw [hd, norm_sub_rev (gradient q s) (gradient f s)] at hp
  rw [norm_sub_rev s w] at ht
  exact hp.trans ht

open ConstrainedMinimaxValue

lemma tilt_value_gradient {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (w e : Space p) (x : p.E) :
    ‖gradient (value f) x - gradient (value (tilt f w e)) x‖ ≤
      (1 + p.L / p.μ) * ‖e‖ := by
  let q := tilt f w e
  have Q : Regularity p q := tilt_regularity H w e
  obtain ⟨y, hy, hm⟩ := attain H hv x
  obtain ⟨v, hvY, hvm⟩ := attain Q hv x
  have hY : Convex ℝ p.Y := hv.2.2.2.2.2.2.2.1
  have hn := strongly_concave_gradient
    (fun a (_ : a ∈ p.Y) b (_ : b ∈ p.Y) => H.strongly_concave x a b) hy hvY
  have h1 := max_variational hY hy hm
    (OracleTemplate.PLMinimax.joint_gradient_snd (H.hasGradient (WithLp.toLp 2 (x, y)))) v hvY
  have h2 := max_variational hY hvY hvm
    (OracleTemplate.PLMinimax.joint_gradient_snd (Q.hasGradient (WithLp.toLp 2 (x, v)))) y hy
  have hs := variational_stability hn h1 h2
  change p.μ * ‖y - v‖ ≤ ‖(gradient f (WithLp.toLp 2 (x, v))).snd -
    (gradient (tilt f w e) (WithLp.toLp 2 (x, v))).snd‖ at hs
  rw [tilt_gradient H] at hs
  change p.μ * ‖y - v‖ ≤ ‖(gradient f (WithLp.toLp 2 (x, v))).snd -
    ((gradient f (WithLp.toLp 2 (x, v))).snd - e.snd)‖ at hs
  rw [sub_sub_cancel] at hs
  have hdist : ‖y - v‖ ≤ ‖e‖ / p.μ := by
    apply (le_div_iff₀ hv.1).mpr
    have hh := hs.trans (WithLp.norm_snd_le p.E e)
    nlinarith
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hg := primal_gradient_lipschitz H hL.le x x y v
  simp only [sub_self, norm_zero, zero_add] at hg
  have hb := hg.trans (mul_le_mul_of_nonneg_left hdist hL.le)
  rw [show p.L * (‖e‖ / p.μ) = (p.L / p.μ) * ‖e‖ by ring] at hb
  rw [(value_hasGradient H hv hy hm).gradient, (value_hasGradient Q hv hvY hvm).gradient]
  change ‖(gradient f (WithLp.toLp 2 (x, y))).fst -
    (gradient (tilt f w e) (WithLp.toLp 2 (x, v))).fst‖ ≤ _
  rw [tilt_gradient H]
  have he : (gradient f (WithLp.toLp 2 (x, y))).fst -
      (gradient f (WithLp.toLp 2 (x, v)) - e).fst =
      ((gradient f (WithLp.toLp 2 (x, y))).fst -
        (gradient f (WithLp.toLp 2 (x, v))).fst) + e.fst := by
    change _ - (_ - _) = _
    abel
  rw [he]
  have ht := norm_add_le ((gradient f (WithLp.toLp 2 (x, y))).fst -
    (gradient f (WithLp.toLp 2 (x, v))).fst) e.fst
  have hp := WithLp.norm_fst_le p.E e
  nlinarith

end LongTails.Proofs.ConstrainedSaddlePerturbation
