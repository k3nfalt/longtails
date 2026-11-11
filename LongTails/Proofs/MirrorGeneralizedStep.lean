import LongTails.Algorithms.MirrorGeneralizedAcceleration
import LongTails.Proofs.MirrorGeneralizedLocal
import LongTails.Proofs.MirrorGeneralizedGeometry
import Mathlib.Analysis.Convex.Deriv

namespace LongTails.Proofs.MirrorGeneralizedStep

open Set LongTails.Setups.MirrorGeneralizedSmooth
open LongTails.Algorithms.MirrorGeneralizedAcceleration

structure Hyp {p : Public} (I : Instance p) : Prop where
  convex : ConvexOn ℝ univ I.f
  grad : ∀ x, HasFDerivAt I.f (I.grad x) x
  cont : Continuous I.grad
  smooth : SegmentSmooth I.grad p.L0 p.L1
  mirror : ∀ x, HasFDerivAt I.ψ (I.mirrorGrad x) x
  strong : ∀ x y, ‖y - x‖ ^ 2 / 2 ≤ bregman I y x
  proximal : ∀ z v, IsMinOn (proxObjective I z v) univ (I.prox z v)

lemma prox_min {p : Public} {I : Instance p} (h : Hyp I)
    (z : p.E) (v : p.E →L[ℝ] ℝ) (u : p.E) :
    v (I.prox z v) + I.ψ (I.prox z v) - I.mirrorGrad z (I.prox z v) ≤
      v u + I.ψ u - I.mirrorGrad z u := by
  have hh := h.proximal z v (mem_univ u)
  dsimp [proxObjective, bregman] at hh
  simp only [map_sub] at hh
  linarith

lemma prox_identity {p : Public} {I : Instance p} (h : Hyp I)
    (z u : p.E) (v : p.E →L[ℝ] ℝ) :
    v (I.prox z v - u) = bregman I u z - bregman I u (I.prox z v) -
      bregman I (I.prox z v) z :=
  MirrorGeneralizedGeometry.prox_three_point h.mirror z (I.prox z v) u v (prox_min h z v)

lemma prox_distance {p : Public} {I : Instance p} (h : Hyp I)
    (z : p.E) (v : p.E →L[ℝ] ℝ) : ‖I.prox z v - z‖ ≤ ‖v‖ :=
  MirrorGeneralizedGeometry.prox_displacement h.mirror h.strong z (I.prox z v) v
    (prox_min h z v)

lemma weight_pos {p : Public} (hL1 : 0 ≤ p.L1) {A M : ℝ} (hA : 0 < A) (hM : 0 < M) :
    0 < weight p A M := by
  have hr : 0 ≤ radius p := by unfold radius; positivity
  unfold weight
  positivity

lemma weight_square {p : Public} (hL1 : 0 ≤ p.L1) {A M : ℝ}
    (hA : 0 < A) (hM : 0 < M) : 64 * M * (weight p A M) ^ 2 ≤ A := by
  have ha := weight_pos hL1 hA hM
  have hb : weight p A M ≤ Real.sqrt (A / (64 * M)) := min_le_left _ _
  have hs := Real.sq_sqrt (show 0 ≤ A / (64 * M) by positivity)
  have hsq : (weight p A M) ^ 2 ≤ A / (64 * M) := by
    nlinarith [Real.sqrt_nonneg (A / (64 * M))]
  have hh := (le_div_iff₀ (show 0 < 64 * M by positivity)).mp hsq
  nlinarith

lemma weight_cap {p : Public} (A M : ℝ) :
    weight p A M ≤ A / (64 * (1 + p.L1 * radius p)) := min_le_right _ _

lemma mix_sub {p : Public} (s : Core p) {a : ℝ} (h : s.A + a ≠ 0) (z : p.E) :
    mix p s a z - s.x = (a / (s.A + a)) • (z - s.x) := by
  have he : s.A / (s.A + a) = 1 - a / (s.A + a) := by field_simp; ring
  simp only [mix, he]
  module

lemma mix_difference {p : Public} (s : Core p) (a : ℝ) (u v : p.E) :
    mix p s a u - mix p s a v = (a / (s.A + a)) • (u - v) := by
  simp only [mix]
  module

lemma convex_support {p : Public} {I : Instance p} (h : Hyp I) (x y : p.E) :
    I.grad x (y - x) ≤ I.f y - I.f x := by
  have hc := h.convex.comp_affineMap (AffineMap.lineMap x y)
  have hd : HasFDerivAt I.f (I.grad x) ((AffineMap.lineMap x y) (0 : ℝ)) := by
    simpa using h.grad x
  have hline : HasDerivAt (I.f ∘ AffineMap.lineMap x y) (I.grad x (y - x)) (0 : ℝ) := by
    simpa using hd.comp_hasDerivAt (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ)))
  have hh := hc.le_slope_of_hasDerivAt (x := 0) (y := 1)
    (by simp) (by simp) (by norm_num) hline
  simpa [slope_def_field] using hh

lemma mix_ball {p : Public} (s : Core p) {a R : ℝ} (hA : 0 < s.A) (ha : 0 ≤ a)
    (u z : p.E) (hx : ‖s.x - u‖ ≤ R) (hz : ‖z - u‖ ≤ R) :
    ‖mix p s a z - u‖ ≤ R := by
  have hsum : 0 < s.A + a := by linarith
  have hα : 0 ≤ s.A / (s.A + a) := by positivity
  have hβ : 0 ≤ a / (s.A + a) := by positivity
  have hweights : s.A / (s.A + a) + a / (s.A + a) = 1 := by
    rw [← add_div, div_self hsum.ne']
  have he : mix p s a z - u = (s.A / (s.A + a)) • (s.x - u) +
      (a / (s.A + a)) • (z - u) := by
    have hu : (s.A / (s.A + a)) • u + (a / (s.A + a)) • u = u := by
      rw [← add_smul, hweights, one_smul]
    calc
      mix p s a z - u = (s.A / (s.A + a)) • s.x + (a / (s.A + a)) • z -
          ((s.A / (s.A + a)) • u + (a / (s.A + a)) • u) := by rw [hu]; rfl
      _ = _ := by module

  rw [he]
  calc
    _ ≤ ‖(s.A / (s.A + a)) • (s.x - u)‖ + ‖(a / (s.A + a)) • (z - u)‖ := norm_add_le _ _
    _ = (s.A / (s.A + a)) * ‖s.x - u‖ + (a / (s.A + a)) * ‖z - u‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hα, abs_of_nonneg hβ]
    _ ≤ (s.A / (s.A + a)) * R + (a / (s.A + a)) * R :=
      add_le_add (mul_le_mul_of_nonneg_left hx hα) (mul_le_mul_of_nonneg_left hz hβ)
    _ = R := by rw [← add_mul, hweights, one_mul]

lemma energy_step_of_upper {p : Public} {I : Instance p} (h : Hyp I)
    (s : Core p) {a M : ℝ} (hA : 0 < s.A) (ha : 0 < a)
    (hcoef : 2 * M * a ^ 2 ≤ s.A + a) (u : p.E)
    (hupper : let y := mix p s a s.z
      let w := I.prox s.z (a • I.grad y)
      I.f (mix p s a w) ≤ I.f y + I.grad y (mix p s a w - y) +
        M * ‖mix p s a w - y‖ ^ 2) :
    let y := mix p s a s.z
    let w := I.prox s.z (a • I.grad y)
    (s.A + a) * (I.f (mix p s a w) - I.f u) + bregman I u w ≤
      s.A * (I.f s.x - I.f u) + bregman I u s.z := by
  dsimp only at hupper ⊢
  set y := mix p s a s.z
  set w := I.prox s.z (a • I.grad y)
  set xp := mix p s a w
  have hp : 0 < s.A + a := by positivity
  have hp0 := hp.ne'
  have hc1 := convex_support h y s.x
  have hc2 := convex_support h y u
  have hi := prox_identity h s.z u (a • I.grad y)
  simp only [smul_apply, smul_eq_mul] at hi
  have he1 : (s.A + a) * I.grad y (xp - y) = a * I.grad y (w - s.z) := by
    dsimp [xp, y]
    rw [mix_difference]
    simp only [map_smul, smul_eq_mul]
    field_simp
  have he2 : s.A * I.grad y (s.x - y) + a * I.grad y (u - y) =
      a * I.grad y (u - s.z) := by
    change s.A * I.grad y (s.x - mix p s a s.z) +
      a * I.grad y (u - mix p s a s.z) = _
    simp only [mix, map_sub, map_add, map_smul, smul_eq_mul]
    field_simp
    ring
  have hnorm : ‖xp - y‖ = (a / (s.A + a)) * ‖w - s.z‖ := by
    dsimp [xp, y]
    rw [mix_difference, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos ha hp)]
  have hquad : (s.A + a) * M * ‖xp - y‖ ^ 2 ≤ ‖w - s.z‖ ^ 2 / 2 := by
    rw [hnorm]
    have hc : M * a ^ 2 / (s.A + a) ≤ 1 / 2 := by
      apply (div_le_iff₀ hp).mpr
      linarith
    calc
      _ = (M * a ^ 2 / (s.A + a)) * ‖w - s.z‖ ^ 2 := by field_simp
      _ ≤ (1 / 2) * ‖w - s.z‖ ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ = _ := by ring
  have hs := h.strong s.z w
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hc1 hA.le)
    (mul_le_mul_of_nonneg_left hc2 ha.le)
  rw [he2] at hsum
  have hup := mul_le_mul_of_nonneg_left hupper hp.le
  change (s.A + a) * I.f xp ≤
    (s.A + a) * (I.f y + I.grad y (xp - y) + M * ‖xp - y‖ ^ 2) at hup
  have hlinear : I.grad y (w - s.z) - I.grad y (u - s.z) = I.grad y (w - u) := by
    simp only [map_sub]; ring
  have hl := congrArg (fun t : ℝ => a * t) hlinear
  nlinarith

lemma query_distance {p : Public} (s : Core p) {a R : ℝ} (hA : 0 < s.A) (ha : 0 < a)
    (hd : ‖s.z - s.x‖ ≤ 2 * R) :
    ‖mix p s a s.z - s.x‖ ≤ 2 * R * a / (s.A + a) := by
  rw [mix_sub s (by positivity), norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos ha (by positivity))]
  calc
    _ ≤ (a / (s.A + a)) * (2 * R) := mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by ring

lemma query_short {p : Public} (s : Core p) {M : ℝ} (hA : 0 < s.A) (hM : 0 < M)
    (hL1 : 0 ≤ p.L1) (hd : ‖s.z - s.x‖ ≤ 2 * radius p) :
    p.L1 * ‖mix p s (weight p s.A M) s.z - s.x‖ ≤ 1 / 32 := by
  set a := weight p s.A M
  have ha : 0 < a := weight_pos hL1 hA hM
  have hr : 0 ≤ radius p := by unfold radius; positivity
  have hc := weight_cap (p := p) s.A M
  have hden : 0 < 64 * (1 + p.L1 * radius p) := by positivity
  have hc' : a * (64 * (1 + p.L1 * radius p)) ≤ s.A :=
    (le_div_iff₀ hden).mp hc
  have hdist := query_distance s hA ha hd
  have hd' := (le_div_iff₀ (show 0 < s.A + a by positivity)).mp hdist
  have hh := mul_le_mul_of_nonneg_left hd' hL1
  have hsum : 0 < s.A + a := by positivity
  nlinarith

lemma prox_mix_distance {p : Public} {I : Instance p} (h : Hyp I) (s : Core p)
    {a : ℝ} (hA : 0 < s.A) (ha : 0 < a) :
    let y := mix p s a s.z
    let w := I.prox s.z (a • I.grad y)
    ‖mix p s a w - y‖ ≤ a ^ 2 * ‖I.grad y‖ / (s.A + a) := by
  dsimp only
  rw [mix_difference, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos ha (by positivity))]
  have hd := prox_distance h s.z (a • I.grad (mix p s a s.z))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at hd
  calc
    _ ≤ (a / (s.A + a)) * (a * ‖I.grad (mix p s a s.z)‖) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by ring

lemma actual_upper {p : Public} {I : Instance p} (h : Hyp I) (s : Core p)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hA : 0 < s.A)
    (hd : ‖s.z - s.x‖ ≤ 2 * radius p) :
    let M := p.L0 + p.L1 * ‖I.grad s.x‖
    let a := weight p s.A M
    let y := mix p s a s.z
    let w := I.prox s.z (a • I.grad y)
    I.f (mix p s a w) ≤ I.f y + I.grad y (mix p s a w - y) +
      M * ‖mix p s a w - y‖ ^ 2 := by
  dsimp only
  set M := p.L0 + p.L1 * ‖I.grad s.x‖
  set a := weight p s.A M
  set y := mix p s a s.z
  set w := I.prox s.z (a • I.grad y)
  set xp := mix p s a w
  have hM : 0 < M := by dsimp [M]; positivity
  have ha : 0 < a := weight_pos hL1 hA hM
  have hq : p.L1 * ‖y - s.x‖ ≤ 1 / 32 := query_short s hA hM hL1 hd
  have hg := MirrorGeneralizedLocal.segment_gradient_bound hL0.le hL1 h.cont h.smooth
    s.x y (by linarith : p.L1 * ‖y - s.x‖ ≤ 1 / 2)
  have hgy : p.L1 * ‖I.grad y‖ ≤ 2 * M := by
    have h1 := mul_le_mul_of_nonneg_left hg hL1
    have h2 := mul_le_mul_of_nonneg_left hq hL0.le
    dsimp [M]
    nlinarith
  have hpdist : ‖xp - y‖ ≤ a ^ 2 * ‖I.grad y‖ / (s.A + a) :=
    prox_mix_distance h s hA ha
  have hwgt : 64 * M * a ^ 2 ≤ s.A := weight_square hL1 hA hM
  have hshort : p.L1 * ‖xp - y‖ ≤ 1 / 32 := by
    have ht := (le_div_iff₀ (show 0 < s.A + a by positivity)).mp hpdist
    have ht' := mul_le_mul_of_nonneg_left ht hL1
    have hg' := mul_le_mul_of_nonneg_right hgy (sq_nonneg a)
    have hp : 0 < s.A + a := by positivity
    nlinarith
  set r := ‖y - s.x‖ + ‖xp - y‖
  have hr : p.L1 * r ≤ 1 / 2 := by dsimp [r]; nlinarith
  have hy : ‖y - s.x‖ ≤ r := le_add_of_nonneg_right (norm_nonneg _)
  have hxp : ‖xp - s.x‖ ≤ r := by
    have ht : ‖xp - s.x‖ ≤ ‖xp - y‖ + ‖y - s.x‖ := by
      calc
        _ = ‖(xp - y) + (y - s.x)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    dsimp [r]
    linarith
  exact MirrorGeneralizedLocal.ball_upper hL0.le hL1 h.grad h.cont h.smooth hr hy hxp

lemma actual_energy {p : Public} {I : Instance p} (h : Hyp I) (s : Core p)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hA : 0 < s.A)
    (hd : ‖s.z - s.x‖ ≤ 2 * radius p) (u : p.E) :
    let M := p.L0 + p.L1 * ‖I.grad s.x‖
    let a := weight p s.A M
    let y := mix p s a s.z
    let w := I.prox s.z (a • I.grad y)
    (s.A + a) * (I.f (mix p s a w) - I.f u) + bregman I u w ≤
      s.A * (I.f s.x - I.f u) + bregman I u s.z := by
  dsimp only
  have hM : 0 < p.L0 + p.L1 * ‖I.grad s.x‖ := by positivity
  have ha := weight_pos hL1 hA hM
  apply energy_step_of_upper h s hA ha _ u (actual_upper h s hL0 hL1 hA hd)
  have hh := weight_square hL1 hA hM
  nlinarith [sq_nonneg (weight p s.A (p.L0 + p.L1 * ‖I.grad s.x‖))]

end LongTails.Proofs.MirrorGeneralizedStep
