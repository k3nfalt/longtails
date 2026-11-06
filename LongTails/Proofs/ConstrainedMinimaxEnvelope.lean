import LongTails.Proofs.ConstrainedMinimaxValue

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.ConstrainedMinimaxEnvelope

open LongTails.Setups.ConstrainedMinimaxSecondOrder
open LongTails.Proofs.ConstrainedMinimaxValue
open OracleTemplate.WeaklyConvexHeavyTailed
open OracleTemplate.PLMinimax (weakProx weakEnvelope weakProx_min weakProx_stationary
  proxObj_min_of_stationary)

lemma value_weak {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) :
    WeakSubgradientOn univ p.L (value f) (gradient (value f)) := by
  intro x _ x' _
  obtain ⟨y, hy, hm⟩ := attain H hv x
  rw [value_eq hy hm, (value_hasGradient H hv hy hm).gradient]
  exact (primal_lower H (hv.1.trans_le hv.2.1).le x x' y).trans (le_value H hv x' hy)

noncomputable def primal {p : Params} (f : Space p → ℝ) (z : p.E) : p.E :=
  weakProx (value f) p.L z

noncomputable def envelope {p : Params} (f : Space p → ℝ) (z : p.E) : ℝ :=
  weakEnvelope (value f) p.L z

noncomputable def dual {p : Params} (f : Space p → ℝ) (z : p.E) : p.F := by
  classical
  exact if h : ∃ y ∈ p.Y, IsMaxOn (fun v => f (WithLp.toLp 2 (primal f z, v))) p.Y y
  then h.choose else p.y0

lemma dual_spec {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) :
    dual f z ∈ p.Y ∧ IsMaxOn (fun v => f (WithLp.toLp 2 (primal f z, v))) p.Y (dual f z) := by
  classical
  have ha := attain H hv (primal f z)
  simp only [dual, dite_eq_left ha]
  exact ha.choose_spec

lemma envelope_hasGradient {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) :
    HasGradientAt (envelope f) ((2 * p.L) • (z - primal f z)) z :=
  OracleTemplate.PLMinimax.weakEnvelope_hasGradient (hv.1.trans_le hv.2.1)
    (value_differentiable H hv).continuous (value_weak H hv) z

lemma envelope_eq {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) :
    envelope f z = f (WithLp.toLp 2 (primal f z, dual f z)) + p.L * ‖primal f z - z‖ ^ 2 := by
  change value f (primal f z) + _ = _
  rw [value_eq (dual_spec H hv z).1 (dual_spec H hv z).2]
  rfl

lemma primal_min {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z x : p.E) :
    value f (primal f z) + p.L * ‖primal f z - z‖ ^ 2 ≤ value f x + p.L * ‖x - z‖ ^ 2 := by
  exact weakProx_min (hv.1.trans_le hv.2.1) (value_differentiable H hv).continuous
    (value_weak H hv) z (mem_univ x)

lemma primal_stationary {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) :
    gradient (value f) (primal f z) + (2 * p.L) • (primal f z - z) = 0 := by
  apply weakProx_stationary (hv.1.trans_le hv.2.1) _ (value_weak H hv) z
  intro x
  obtain ⟨y, hy, hm⟩ := attain H hv x
  rw [(value_hasGradient H hv hy hm).gradient]
  exact value_hasGradient H hv hy hm

lemma saddle_primal_zero {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) :
    (gradient f (WithLp.toLp 2 (primal f z, dual f z))).fst +
      (2 * p.L) • (primal f z - z) = 0 := by
  have hs := primal_stationary H hv z
  rw [(value_hasGradient H hv (dual_spec H hv z).1 (dual_spec H hv z).2).gradient] at hs
  exact hs

lemma saddle_dual_normal {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) :
    ∀ v ∈ p.Y, ⟪(gradient f (WithLp.toLp 2 (primal f z, dual f z))).snd, v - dual f z⟫ ≤ 0 :=
  max_variational hv.2.2.2.2.2.2.2.1 (dual_spec H hv z).1 (dual_spec H hv z).2
    (OracleTemplate.PLMinimax.joint_gradient_snd (H.hasGradient _))

lemma saddle_center_energy {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z z' : p.E) :
    p.L * ‖primal f z - primal f z'‖ ^ 2 + p.μ * ‖dual f z - dual f z'‖ ^ 2 ≤
      2 * p.L * ⟪z - z', primal f z - primal f z'⟫ := by
  have hm := ConstrainedSaddleGeometry.regularized_monotonicity
    (fun x x' y => primal_lower H (hv.1.trans_le hv.2.1).le x x' y)
    H.strongly_concave (primal f z) (primal f z') (0 : p.E) (dual f z) (dual f z')
  have he (t : p.E) : (gradient f (WithLp.toLp 2 (primal f t, dual f t))).fst +
      (2 * p.L) • (primal f t - 0) = (2 * p.L) • t := by
    have hs := saddle_primal_zero H hv t
    have hh : (gradient f (WithLp.toLp 2 (primal f t, dual f t))).fst +
        (2 * p.L) • (primal f t - 0) =
        ((gradient f (WithLp.toLp 2 (primal f t, dual f t))).fst +
          (2 * p.L) • (primal f t - t)) + (2 * p.L) • t := by module
    rw [hh, hs, zero_add]
  rw [he z, he z', ← smul_sub, real_inner_smul_left] at hm
  simp only [inner_sub_left] at hm ⊢
  have h1 := saddle_dual_normal H hv z (dual f z') (dual_spec H hv z').1
  have h2 := saddle_dual_normal H hv z' (dual f z) (dual_spec H hv z).1
  rw [show dual f z' - dual f z = -(dual f z - dual f z') by abel, inner_neg_right] at h1
  linarith

lemma saddle_center_distance_sq {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z z' : p.E) :
    ‖primal f z - primal f z'‖ ^ 2 + ‖dual f z - dual f z'‖ ^ 2 ≤
      (4 + p.L / p.μ) * ‖z - z'‖ ^ 2 :=
  OracleTemplate.PLMinimax.lift_energy (hv.1.trans_le hv.2.1) hv.1
    (z - z') (primal f z - primal f z') (dual f z - dual f z') (saddle_center_energy H hv z z')

lemma saddle_identify {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z u : p.E) (v : p.F) (hmem : v ∈ p.Y)
    (hx : (gradient f (WithLp.toLp 2 (u, v))).fst + (2 * p.L) • (u - z) = 0)
    (hy : ∀ y ∈ p.Y, ⟪(gradient f (WithLp.toLp 2 (u, v))).snd, y - v⟫ ≤ 0) :
    primal f z = u ∧ dual f z = v := by
  have hm := ConstrainedSaddleGeometry.regularized_monotonicity
    (fun x x' y => primal_lower H (hv.1.trans_le hv.2.1).le x x' y)
    H.strongly_concave (primal f z) u z (dual f z) v
  rw [saddle_primal_zero H hv z, hx, sub_self, inner_zero_left, zero_sub, inner_sub_left] at hm
  have h1 := saddle_dual_normal H hv z v hmem
  have h2 := hy (dual f z) (dual_spec H hv z).1
  rw [show v - dual f z = -(dual f z - v) by abel, inner_neg_right] at h1
  have hL := hv.1.trans_le hv.2.1
  have hp := mul_nonneg hL.le (sq_nonneg ‖primal f z - u‖)
  have hq := mul_nonneg hv.1.le (sq_nonneg ‖dual f z - v‖)
  have hx0 : ‖primal f z - u‖ ^ 2 ≤ 0 := by
    apply le_of_mul_le_mul_left (a := p.L) _ hL
    linarith
  have hy0 : ‖dual f z - v‖ ^ 2 ≤ 0 := by
    apply le_of_mul_le_mul_left (a := p.μ) _ hv.1
    linarith
  have hxn : ‖primal f z - u‖ = 0 := by nlinarith [sq_nonneg ‖primal f z - u‖]
  have hyn : ‖dual f z - v‖ = 0 := by nlinarith [sq_nonneg ‖dual f z - v‖]
  exact ⟨sub_eq_zero.mp (norm_eq_zero.mp hxn), sub_eq_zero.mp (norm_eq_zero.mp hyn)⟩

lemma primal_center_distance_sq {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z z' : p.E) :
    ‖primal f z - primal f z'‖ ^ 2 ≤ 4 * ‖z - z'‖ ^ 2 := by
  have hh := OracleTemplate.PLMinimax.weakProx_lipschitz (hv.1.trans_le hv.2.1)
    (value_differentiable H hv).continuous (value_weak H hv) z z'
  change ‖primal f z - primal f z'‖ ≤ 2 * ‖z - z'‖ at hh
  nlinarith [norm_nonneg (primal f z - primal f z'), norm_nonneg (z - z')]

lemma dual_center_distance_sq {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z z' : p.E) :
    ‖dual f z - dual f z'‖ ^ 2 ≤ p.L / p.μ * ‖z - z'‖ ^ 2 := by
  have hh := saddle_center_energy H hv z z'
  have he := norm_sub_sq_real (primal f z - primal f z') (z - z')
  rw [real_inner_comm] at he
  have hp := mul_nonneg (hv.1.trans_le hv.2.1).le
    (sq_nonneg ‖(primal f z - primal f z') - (z - z')‖)
  rw [he] at hp
  rw [div_mul_eq_mul_div, le_div_iff₀ hv.1]
  nlinarith

lemma saddle_perturbation_energy {p : Params} {f q : Space p → ℝ}
    (H : Regularity p f) (Q : Regularity p q) (hv : spec.valid p) (z : p.E) :
    let r := gradient f (WithLp.toLp 2 (primal q z, dual q z)) -
      gradient q (WithLp.toLp 2 (primal q z, dual q z))
    p.L * ‖primal f z - primal q z‖ ^ 2 + p.μ * ‖dual f z - dual q z‖ ^ 2 ≤
      ⟪-r.fst, primal f z - primal q z⟫ + ⟪r.snd, dual f z - dual q z⟫ := by
  let r := gradient f (WithLp.toLp 2 (primal q z, dual q z)) -
    gradient q (WithLp.toLp 2 (primal q z, dual q z))
  have hm := ConstrainedSaddleGeometry.regularized_monotonicity
    (fun x x' y => primal_lower H (hv.1.trans_le hv.2.1).le x x' y)
    H.strongly_concave (primal f z) (primal q z) z (dual f z) (dual q z)
  have he : (gradient f (WithLp.toLp 2 (primal f z, dual f z))).fst +
      (2 * p.L) • (primal f z - z) -
      ((gradient f (WithLp.toLp 2 (primal q z, dual q z))).fst +
        (2 * p.L) • (primal q z - z)) = -r.fst := by
    rw [saddle_primal_zero H hv z]
    have hs := saddle_primal_zero Q hv z
    change 0 - _ = -((gradient f _).fst - (gradient q _).fst)
    rw [add_eq_zero_iff_eq_neg] at hs
    rw [hs]
    module
  rw [he, inner_sub_left] at hm
  have h1 := saddle_dual_normal H hv z (dual q z) (dual_spec Q hv z).1
  have h2 := saddle_dual_normal Q hv z (dual f z) (dual_spec H hv z).1
  rw [show dual q z - dual f z = -(dual f z - dual q z) by abel, inner_neg_right] at h1
  have henergy : p.L * ‖primal f z - primal q z‖ ^ 2 + p.μ * ‖dual f z - dual q z‖ ^ 2 ≤
      ⟪-r.fst, primal f z - primal q z⟫ + ⟪r.snd, dual f z - dual q z⟫ := by
    dsimp [r] at hm ⊢
    simp only [inner_sub_left] at *
    linarith
  exact henergy

lemma saddle_perturbation_norm {p : Params} {f q : Space p → ℝ}
    (H : Regularity p f) (Q : Regularity p q) (hv : spec.valid p) (z : p.E) :
    p.μ * ‖WithLp.toLp 2 (primal f z - primal q z, dual f z - dual q z)‖ ≤
      ‖gradient f (WithLp.toLp 2 (primal q z, dual q z)) -
        gradient q (WithLp.toLp 2 (primal q z, dual q z))‖ := by
  let r := gradient f (WithLp.toLp 2 (primal q z, dual q z)) -
    gradient q (WithLp.toLp 2 (primal q z, dual q z))
  let d : Space p := WithLp.toLp 2 (primal f z - primal q z, dual f z - dual q z)
  let a : Space p := WithLp.toLp 2 (-r.fst, r.snd)
  have hn : ‖a‖ = ‖r‖ := by
    have ha := WithLp.prod_norm_sq_eq_of_L2 a
    have hr := WithLp.prod_norm_sq_eq_of_L2 r
    change ‖a‖ ^ 2 = ‖-r.fst‖ ^ 2 + ‖r.snd‖ ^ 2 at ha
    rw [norm_neg] at ha
    nlinarith [norm_nonneg a, norm_nonneg r]
  have he := saddle_perturbation_energy H Q hv z
  change p.L * ‖primal f z - primal q z‖ ^ 2 + p.μ * ‖dual f z - dual q z‖ ^ 2 ≤
    ⟪-r.fst, primal f z - primal q z⟫ + ⟪r.snd, dual f z - dual q z⟫ at he
  have hd := WithLp.prod_norm_sq_eq_of_L2 d
  have hi : p.μ * ‖d‖ ^ 2 ≤ ⟪a, d⟫ := by
    change p.μ * ‖d‖ ^ 2 ≤
      ⟪-r.fst, primal f z - primal q z⟫ + ⟪r.snd, dual f z - dual q z⟫
    change ‖d‖ ^ 2 = ‖primal f z - primal q z‖ ^ 2 +
      ‖dual f z - dual q z‖ ^ 2 at hd
    rw [hd, mul_add]
    apply le_trans (b := p.L * ‖primal f z - primal q z‖ ^ 2 +
      p.μ * ‖dual f z - dual q z‖ ^ 2) _ he
    gcongr
    exact hv.2.1
  have hc := real_inner_le_norm a d
  rw [hn] at hc
  change p.μ * ‖d‖ ≤ ‖r‖
  by_cases hz : ‖d‖ = 0
  · rw [hz, mul_zero]
    exact norm_nonneg r
  · have hp : 0 < ‖d‖ := lt_of_le_of_ne (norm_nonneg d) (Ne.symm hz)
    nlinarith

lemma envelope_gradient_perturbation_sq {p : Params} {f q : Space p → ℝ}
    (H : Regularity p f) (Q : Regularity p q) (hv : spec.valid p) (z : p.E) :
    ‖gradient (envelope f) z - gradient (envelope q) z‖ ^ 2 ≤
      4 * (p.L / p.μ) * ‖gradient f (WithLp.toLp 2 (primal q z, dual q z)) -
        gradient q (WithLp.toLp 2 (primal q z, dual q z))‖ ^ 2 := by
  let r := gradient f (WithLp.toLp 2 (primal q z, dual q z)) -
    gradient q (WithLp.toLp 2 (primal q z, dual q z))
  have henergy := saddle_perturbation_energy H Q hv z
  have hw := ConstrainedSaddleGeometry.weighted_residual_stability
    (hv.1.trans_le hv.2.1) hv.1 henergy
  rw [norm_neg] at hw
  have hk : 1 ≤ p.L / p.μ := (le_div_iff₀ hv.1).mpr (by simpa using hv.2.1)
  have hn := WithLp.prod_norm_sq_eq_of_L2 r
  have hb : p.L ^ 2 * ‖primal f z - primal q z‖ ^ 2 ≤ p.L / p.μ * ‖r‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hk (sq_nonneg ‖r.fst‖)]
  rw [(envelope_hasGradient H hv z).gradient, (envelope_hasGradient Q hv z).gradient,
    ← smul_sub]
  have hd : (z - primal f z) - (z - primal q z) = -(primal f z - primal q z) := by abel
  rw [hd, norm_smul, norm_neg, Real.norm_eq_abs, mul_pow, sq_abs]
  change _ ≤ 4 * (p.L / p.μ) * ‖r‖ ^ 2
  nlinarith

lemma saddle_primal_min {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z u : p.E) :
    f (WithLp.toLp 2 (primal f z, dual f z)) + p.L * ‖primal f z - z‖ ^ 2 ≤
      f (WithLp.toLp 2 (u, dual f z)) + p.L * ‖u - z‖ ^ 2 := by
  have hw : WeakSubgradientOn univ p.L
      (fun x => f (WithLp.toLp 2 (x, dual f z)))
      (fun x => (gradient f (WithLp.toLp 2 (x, dual f z))).fst) := by
    intro x _ x' _
    exact primal_lower H (hv.1.trans_le hv.2.1).le x x' (dual f z)
  exact proxObj_min_of_stationary (hv.1.trans_le hv.2.1).le hw
    (saddle_primal_zero H hv z) (mem_univ u)

lemma envelope_value_comparison {p : Params} {f q : Space p → ℝ}
    (H : Regularity p f) (Q : Regularity p q) (hv : spec.valid p) (z : p.E) {a : ℝ}
    (h1 : |f (WithLp.toLp 2 (primal q z, dual f z)) -
      q (WithLp.toLp 2 (primal q z, dual f z))| ≤ a)
    (h2 : |f (WithLp.toLp 2 (primal f z, dual q z)) -
      q (WithLp.toLp 2 (primal f z, dual q z))| ≤ a) :
    |envelope f z - envelope q z| ≤ a := by
  have hminf := saddle_primal_min H hv z (primal q z)
  have hminq := saddle_primal_min Q hv z (primal f z)
  have hmaxf := (dual_spec H hv z).2 (dual_spec Q hv z).1
  have hmaxq := (dual_spec Q hv z).2 (dual_spec H hv z).1
  change f (WithLp.toLp 2 (primal f z, dual q z)) ≤
    f (WithLp.toLp 2 (primal f z, dual f z)) at hmaxf
  change q (WithLp.toLp 2 (primal q z, dual f z)) ≤
    q (WithLp.toLp 2 (primal q z, dual q z)) at hmaxq
  rw [envelope_eq H hv, envelope_eq Q hv, abs_le]
  obtain ⟨h1l, h1u⟩ := abs_le.mp h1
  obtain ⟨h2l, h2u⟩ := abs_le.mp h2
  constructor <;> linarith

lemma saddle_exists {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) :
    ∃ y ∈ p.Y,
      (∀ v ∈ p.Y, f (WithLp.toLp 2 (primal f z, v)) ≤ f (WithLp.toLp 2 (primal f z, y))) ∧
      (∀ u, f (WithLp.toLp 2 (primal f z, y)) + p.L * ‖primal f z - z‖ ^ 2 ≤
        f (WithLp.toLp 2 (u, y)) + p.L * ‖u - z‖ ^ 2) := by
  exact ⟨dual f z, (dual_spec H hv z).1, (dual_spec H hv z).2, saddle_primal_min H hv z⟩

end LongTails.Proofs.ConstrainedMinimaxEnvelope
