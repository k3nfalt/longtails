import LongTails.Proofs.PLMinimaxGeometry
import LongTails.Proofs.TwoSidedPLEnvelope

open Set InnerProductSpace Filter Topology
open scoped RealInnerProductSpace
open LongTails.Setups.StochasticTwoSidedPL

namespace OracleTemplate.PLMinimax

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

structure Hyp (f : E → F → ℝ) (gx : E → F → E) (gy : E → F → F) (L μ : ℝ) : Prop where
  hL : 0 < L
  hμ : 0 < μ
  hμL : μ ≤ L
  hgx : ∀ x y, HasGradientAt (fun x => f x y) (gx x y) x
  hgy : ∀ x y, HasGradientAt (f x) (gy x y) y
  lipx : ∀ x x' y y', ‖gx x y - gx x' y'‖ ≤ L * (‖x - x'‖ + ‖y - y'‖)
  lipy : ∀ x x' y y', ‖gy x y - gy x' y'‖ ≤ L * (‖x - x'‖ + ‖y - y'‖)
  ply : ∀ x y y', 2 * μ * (f x y' - f x y) ≤ ‖gy x y‖ ^ 2
  attain : ∀ x, ∃ y, ∀ y', f x y' ≤ f x y

variable {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ : ℝ}

lemma Hyp.near_max [FiniteDimensional ℝ F] (H : Hyp f gx gy L μ) (x : E) (y : F) :
    ∃ p, (∀ y', f x y' ≤ f x p) ∧ μ ^ 2 * ‖y - p‖ ^ 2 ≤ 8 * ‖gy x y‖ ^ 2 := by
  obtain ⟨u, hu⟩ := H.attain x
  have hg : ∀ v, HasGradientAt (fun y => -f x y) (-gy x v) v :=
    fun v => TwoSidedPL.hasGradientAt_neg' (H.hgy x v)
  have he : ∀ v, gradient (fun y => -f x y) v = -gy x v := fun v => (hg v).gradient
  obtain ⟨p, hp, hd⟩ := pl_error_bound (f := fun v => -f x v) H.hL H.hμ H.hμL
    (fun v => by rw [he]; exact hg v)
    (fun a b => by
      rw [he, he, neg_sub_neg, norm_sub_rev]
      simpa using H.lipy x x a b)
    (u := u) (fun v _ => neg_le_neg (hu v)) (fun v => by
      rw [he, norm_neg]
      simpa only [neg_sub_neg] using H.ply x v u) y
  refine ⟨p, fun v => ?_, ?_⟩
  · have := hp (mem_univ v)
    simpa using this
  · simpa [he] using hd

lemma Hyp.max_gradient_zero (H : Hyp f gx gy L μ) {x : E} {y : F}
    (hy : ∀ v, f x v ≤ f x y) : gy x y = 0 := by
  have hmin : IsMinOn (fun v => -f x v) univ y := fun v _ => neg_le_neg (hy v)
  have hg := TwoSidedPL.hasGradientAt_neg' (H.hgy x y)
  have hzero := (hmin.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero hg.hasFDerivAt
  have hz' : -gy x y = 0 := by
    apply (toDual ℝ F).injective
    simpa using hzero
  simpa using hz'

lemma Hyp.nearby_max [FiniteDimensional ℝ F] (H : Hyp f gx gy L μ)
    {x : E} {y : F} (hy : ∀ v, f x v ≤ f x y) (x' : E) :
    ∃ y', (∀ v, f x' v ≤ f x' y') ∧
      μ ^ 2 * ‖y - y'‖ ^ 2 ≤ 8 * L ^ 2 * ‖x - x'‖ ^ 2 := by
  have hz := H.max_gradient_zero hy
  obtain ⟨y', hy', hd⟩ := H.near_max x' y
  refine ⟨y', hy', hd.trans ?_⟩
  have hl : ‖gy x' y‖ ≤ L * ‖x - x'‖ := by
    have := H.lipy x' x y y
    simpa [hz, norm_sub_rev] using this
  have hr : 0 ≤ L * ‖x - x'‖ := mul_nonneg H.hL.le (norm_nonneg _)
  nlinarith [norm_nonneg (gy x' y)]

lemma Hyp.max_value_eq (_H : Hyp f gx gy L μ) {x : E} {y : F}
    (hy : ∀ v, f x v ≤ f x y) : maxValue f x = f x y := by
  apply le_antisymm (ciSup_le hy)
  exact le_ciSup ⟨f x y, by rintro _ ⟨v, rfl⟩; exact hy v⟩ y

lemma Hyp.le_max_value (H : Hyp f gx gy L μ) (x : E) (y : F) : f x y ≤ maxValue f x := by
  obtain ⟨v, hv⟩ := H.attain x
  rw [H.max_value_eq hv]
  exact hv y

lemma Hyp.upper_x (H : Hyp f gx gy L μ) (x x' : E) (y : F) :
    f x' y ≤ f x y + ⟪gx x y, x' - x⟫ + L / 2 * ‖x' - x‖ ^ 2 :=
  Gradient.smooth_upper_bound (fun x => H.hgx x y)
    (fun a b => by simpa using H.lipx a b y y) x x'

lemma Hyp.lower_x (H : Hyp f gx gy L μ) (x x' : E) (y : F) :
    f x y + ⟪gx x y, x' - x⟫ - L / 2 * ‖x' - x‖ ^ 2 ≤ f x' y := by
  have hh := Gradient.smooth_upper_bound (f := fun x => -f x y) (oracle := fun x => -gx x y)
    (L := L) (fun x => TwoSidedPL.hasGradientAt_neg' (H.hgx x y))
    (fun a b => by rw [neg_sub_neg, norm_sub_rev]; simpa using H.lipx a b y y) x x'
  simp only [inner_neg_left] at hh
  linarith

lemma Hyp.value_remainder [FiniteDimensional ℝ F] (H : Hyp f gx gy L μ)
    {x : E} {y : F} (hy : ∀ v, f x v ≤ f x y) (h : E) :
    |maxValue f (x + h) - maxValue f x - ⟪gx x y, h⟫| ≤
      (L + 3 * L ^ 2 / μ) * ‖h‖ ^ 2 := by
  obtain ⟨v, hv, hd⟩ := H.nearby_max hy (x + h)
  have hd' : μ * ‖y - v‖ ≤ 3 * L * ‖h‖ := by
    simp only [sub_add_cancel_left, norm_neg] at hd
    have ha : 0 ≤ μ * ‖y - v‖ := mul_nonneg H.hμ.le (norm_nonneg _)
    have hb : 0 ≤ 3 * L * ‖h‖ := by have := H.hL; positivity
    nlinarith [sq_nonneg (μ * ‖y - v‖ - 3 * L * ‖h‖)]
  have hl : ‖gx x v - gx x y‖ ≤ 3 * L ^ 2 / μ * ‖h‖ := by
    have hl := H.lipx x x v y
    simp only [sub_self, norm_zero, zero_add, norm_sub_rev v y] at hl
    have hμ := H.hμ
    rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
    nlinarith [mul_le_mul_of_nonneg_left hd' H.hL.le]
  have hi : ⟪gx x v, h⟫ ≤ ⟪gx x y, h⟫ + 3 * L ^ 2 / μ * ‖h‖ ^ 2 := by
    have hi := real_inner_le_norm (gx x v - gx x y) h
    rw [inner_sub_left] at hi
    nlinarith [mul_le_mul_of_nonneg_right hl (norm_nonneg h)]
  have hu := H.upper_x x (x + h) v
  have hlo := H.lower_x x (x + h) y
  have hmax := H.le_max_value (x + h) y
  have hxy := hy v
  rw [H.max_value_eq hy, H.max_value_eq hv] at *
  simp only [add_sub_cancel_left] at hu hlo
  have hp : 0 ≤ (3 * L ^ 2 / μ) * ‖h‖ ^ 2 := by have := H.hμ; positivity
  have hL := H.hL
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ‖h‖]

lemma Hyp.value_hasGradient [FiniteDimensional ℝ F] (H : Hyp f gx gy L μ)
    {x : E} {y : F} (hy : ∀ v, f x v ≤ f x y) :
    HasGradientAt (maxValue f) (gx x y) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  apply hasFDerivAt_of_quadratic_remainder (C := L + 3 * L ^ 2 / μ)
  intro h
  simpa [Real.norm_eq_abs] using H.value_remainder hy h

lemma Hyp.value_gradient_lipschitz [FiniteDimensional ℝ F] (H : Hyp f gx gy L μ)
    (x x' : E) :
    ‖gradient (maxValue f) x - gradient (maxValue f) x'‖ ≤ (4 * L ^ 2 / μ) * ‖x - x'‖ := by
  obtain ⟨y, hy⟩ := H.attain x
  obtain ⟨y', hy', hd⟩ := H.nearby_max hy x'
  have hd' : μ * ‖y - y'‖ ≤ 3 * L * ‖x - x'‖ := by
    have ha : 0 ≤ μ * ‖y - y'‖ := mul_nonneg H.hμ.le (norm_nonneg _)
    have hb : 0 ≤ 3 * L * ‖x - x'‖ := by have := H.hL; positivity
    nlinarith [sq_nonneg (μ * ‖y - y'‖ - 3 * L * ‖x - x'‖)]
  rw [(H.value_hasGradient hy).gradient, (H.value_hasGradient hy').gradient]
  have hl := H.lipx x x' y y'
  have hμ := H.hμ
  rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
  have hm := mul_le_mul_of_nonneg_left hl hμ.le
  have hp := mul_le_mul_of_nonneg_left hd' H.hL.le
  have hμL := mul_le_mul_of_nonneg_right H.hμL
    (show 0 ≤ L * ‖x - x'‖ by have := H.hL; positivity)
  nlinarith

end OracleTemplate.PLMinimax
