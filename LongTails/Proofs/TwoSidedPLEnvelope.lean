import LongTails.Proofs.GdConvex
import LongTails.Setups.StochasticTwoSidedPL
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set InnerProductSpace Filter Topology
open scoped RealInnerProductSpace
open LongTails.Setups.StochasticTwoSidedPL

namespace OracleTemplate.TwoSidedPL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

structure Hyp (f : E → F → ℝ) (gx : E → F → E) (gy : E → F → F) (L μx μy : ℝ) : Prop where
  hL : 0 < L
  hμx : 0 < μx
  hμxL : μx ≤ L
  hμy : 0 < μy
  hμyL : μy ≤ L
  hgx : ∀ x y, HasGradientAt (fun x => f x y) (gx x y) x
  hgy : ∀ x y, HasGradientAt (f x) (gy x y) y
  lipx : ∀ x x' y y', ‖gx x y - gx x' y'‖ ≤ L * (‖x - x'‖ + ‖y - y'‖)
  lipy : ∀ x x' y y', ‖gy x y - gy x' y'‖ ≤ L * (‖x - x'‖ + ‖y - y'‖)
  plx : ∀ x x' y, 2 * μx * (f x y - f x' y) ≤ ‖gx x y‖ ^ 2
  ply : ∀ x y y', 2 * μy * (f x y' - f x y) ≤ ‖gy x y‖ ^ 2
  attain : ∀ x, ∃ y, ∀ y', f x y' ≤ f x y

noncomputable def fhat (f : E → F → ℝ) (L : ℝ) (z x : E) (y : F) : ℝ := f x y + L * ‖x - z‖ ^ 2

noncomputable def xhat (f : E → F → ℝ) (L : ℝ) (y : F) (z : E) : E :=
  Classical.epsilon (fun x => ∀ x', fhat f L z x y ≤ fhat f L z x' y)

noncomputable def psi (f : E → F → ℝ) (L : ℝ) (y : F) (z : E) : ℝ := fhat f L z (xhat f L y z) y

noncomputable def phat (f : E → F → ℝ) (L : ℝ) (z x : E) : ℝ := maxValue f x + L * ‖x - z‖ ^ 2

noncomputable def xbar (f : E → F → ℝ) (L : ℝ) (z : E) : E :=
  Classical.epsilon (fun x => ∀ x', phat f L z x ≤ phat f L z x')

noncomputable def envelope (f : E → F → ℝ) (L : ℝ) (z : E) : ℝ := phat f L z (xbar f L z)

lemma hasGradientAt_neg' {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    {φ : G → ℝ} {g x : G} (h : HasGradientAt φ g x) : HasGradientAt (fun x => -φ x) (-g) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at h ⊢
  rw [map_neg]
  exact h.neg

section Smooth

variable {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μx μy : ℝ}

lemma Hyp.upper_x (H : Hyp f gx gy L μx μy) (x x' : E) (y : F) :
    f x' y ≤ f x y + ⟪gx x y, x' - x⟫ + L / 2 * ‖x' - x‖ ^ 2 :=
  Gradient.smooth_upper_bound (f := fun x => f x y) (oracle := fun x => gx x y)
    (fun x => H.hgx x y) (fun a b => by simpa using H.lipx a b y y) x x'

lemma Hyp.lower_x (H : Hyp f gx gy L μx μy) (x x' : E) (y : F) :
    f x y + ⟪gx x y, x' - x⟫ - L / 2 * ‖x' - x‖ ^ 2 ≤ f x' y := by
  have h := Gradient.smooth_upper_bound (f := fun x => -f x y) (oracle := fun x => -gx x y)
    (L := L) (fun x => hasGradientAt_neg' (H.hgx x y)) (fun a b => by
      rw [show -gx a y - -gx b y = gx b y - gx a y by abel, norm_sub_rev a b]
      simpa using H.lipx b a y y) x x'
  simp only [inner_neg_left] at h
  linarith

lemma Hyp.upper_y (H : Hyp f gx gy L μx μy) (x : E) (y y' : F) :
    f x y' ≤ f x y + ⟪gy x y, y' - y⟫ + L / 2 * ‖y' - y‖ ^ 2 :=
  Gradient.smooth_upper_bound (f := f x) (oracle := fun y => gy x y)
    (fun y => H.hgy x y) (fun a b => by simpa using H.lipy x x a b) y y'

lemma Hyp.lower_y (H : Hyp f gx gy L μx μy) (x : E) (y y' : F) :
    f x y + ⟪gy x y, y' - y⟫ - L / 2 * ‖y' - y‖ ^ 2 ≤ f x y' := by
  have h := Gradient.smooth_upper_bound (f := fun y => -f x y) (oracle := fun y => -gy x y)
    (L := L) (fun y => hasGradientAt_neg' (H.hgy x y)) (fun a b => by
      rw [show -gy x a - -gy x b = gy x b - gy x a by abel, norm_sub_rev a b]
      simpa using H.lipy x x b a) y y'
  simp only [inner_neg_left] at h
  linarith

lemma Hyp.bddAbove (H : Hyp f gx gy L μx μy) (x : E) : BddAbove (range (f x)) := by
  obtain ⟨y, hy⟩ := H.attain x
  exact ⟨f x y, by rintro _ ⟨y', rfl⟩; exact hy y'⟩

lemma Hyp.le_maxValue (H : Hyp f gx gy L μx μy) (x : E) (y : F) : f x y ≤ maxValue f x :=
  le_ciSup (H.bddAbove x) y

lemma Hyp.maxValue_attained (H : Hyp f gx gy L μx μy) (x : E) : ∃ y, maxValue f x = f x y := by
  obtain ⟨y, hy⟩ := H.attain x
  exact ⟨y, le_antisymm (ciSup_le hy) (H.le_maxValue x y)⟩

lemma Hyp.maxValue_sub_le (H : Hyp f gx gy L μx μy) (x : E) (y : F) :
    maxValue f x - f x y ≤ ‖gy x y‖ ^ 2 / (2 * μy) := by
  obtain ⟨y', hy'⟩ := H.maxValue_attained x
  rw [hy', le_div_iff₀ (by linarith [H.hμy])]
  linarith [H.ply x y y']

lemma Hyp.maxValue_lower (H : Hyp f gx gy L μx μy) (x0 : E) (y0 : F) (x : E) :
    f x0 y0 - ‖gx x0 y0‖ ^ 2 / (2 * μx) ≤ maxValue f x := by
  have h := H.plx x0 x y0
  have : f x0 y0 - ‖gx x0 y0‖ ^ 2 / (2 * μx) ≤ f x y0 := by
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ (by linarith [H.hμx])]
    linarith
  exact this.trans (H.le_maxValue x y0)

lemma Hyp.bddBelow (H : Hyp f gx gy L μx μy) : BddBelow (range (maxValue f)) := by
  obtain ⟨y0⟩ : Nonempty F := ⟨0⟩
  exact ⟨f 0 y0 - ‖gx 0 y0‖ ^ 2 / (2 * μx), by
    rintro _ ⟨x, rfl⟩; exact H.maxValue_lower 0 y0 x⟩

lemma Hyp.minimax_le (H : Hyp f gx gy L μx μy) (x : E) : minimaxValue f ≤ maxValue f x :=
  ciInf_le H.bddBelow x

lemma Hyp.sub_minimax_le (H : Hyp f gx gy L μx μy) (x : E) (y : F) :
    f x y - minimaxValue f ≤ ‖gx x y‖ ^ 2 / (2 * μx) := by
  have h : f x y - ‖gx x y‖ ^ 2 / (2 * μx) ≤ minimaxValue f := by
    apply le_ciInf
    intro x'
    have h1 := H.plx x x' y
    have : f x y - ‖gx x y‖ ^ 2 / (2 * μx) ≤ f x' y := by
      rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ (by linarith [H.hμx])]
      linarith
    exact this.trans (H.le_maxValue x' y)
  linarith

lemma Hyp.continuous_x (H : Hyp f gx gy L μx μy) (y : F) : Continuous fun x => f x y :=
  continuous_iff_continuousAt.2 fun x => (H.hgx x y).continuousAt

lemma Hyp.lsc_maxValue (H : Hyp f gx gy L μx μy) : LowerSemicontinuous (maxValue f) := by
  have := lowerSemicontinuous_ciSup (f := fun y x => f x y) (fun x => H.bddAbove x)
    (fun y => (H.continuous_x y).lowerSemicontinuous)
  exact this

end Smooth

section Hat

variable {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μx μy : ℝ}

omit [CompleteSpace E] in
lemma norm_sq_expand (x x' z : E) :
    ‖x' - z‖ ^ 2 = ‖x - z‖ ^ 2 + 2 * ⟪x - z, x' - x⟫ + ‖x' - x‖ ^ 2 := by
  have : x' - z = (x - z) + (x' - x) := by abel
  rw [this, norm_add_sq_real]

lemma Hyp.fhat_lower (H : Hyp f gx gy L μx μy) (z x x' : E) (y : F) :
    fhat f L z x y + ⟪gx x y + (2 * L) • (x - z), x' - x⟫ + L / 2 * ‖x' - x‖ ^ 2 ≤
      fhat f L z x' y := by
  have h := H.lower_x x x' y
  have he := norm_sq_expand x x' z
  simp only [fhat, inner_add_left, real_inner_smul_left]
  rw [he]
  nlinarith

lemma Hyp.fhat_upper (H : Hyp f gx gy L μx μy) (z x x' : E) (y : F) :
    fhat f L z x' y ≤
      fhat f L z x y + ⟪gx x y + (2 * L) • (x - z), x' - x⟫ + 3 * L / 2 * ‖x' - x‖ ^ 2 := by
  have h := H.upper_x x x' y
  have he := norm_sq_expand x x' z
  simp only [fhat, inner_add_left, real_inner_smul_left]
  rw [he]
  nlinarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma exists_min_of_growth [ProperSpace E] (φ : E → ℝ) (hφ : LowerSemicontinuous φ) (z : E)
    (R : ℝ) (h : ∀ x, R < ‖x - z‖ → φ z ≤ φ x) : ∃ x, ∀ x', φ x ≤ φ x' := by
  have hR : 0 ≤ max R 0 := le_max_right _ _
  obtain ⟨a, _, ha⟩ := LowerSemicontinuousOn.exists_isMinOn
    (s := Metric.closedBall z (max R 0)) ⟨z, Metric.mem_closedBall_self hR⟩
    (isCompact_closedBall z _) (hφ.lowerSemicontinuousOn _)
  refine ⟨a, fun x' => ?_⟩
  by_cases hx : x' ∈ Metric.closedBall z (max R 0)
  · exact isMinOn_iff.1 ha x' hx
  · have hz := isMinOn_iff.1 ha z (Metric.mem_closedBall_self hR)
    have : R < ‖x' - z‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hx
      exact lt_of_le_of_lt (le_max_left _ _) hx
    exact hz.trans (h x' this)

lemma growth_radius {L a b s : ℝ} (hL : 0 < L) (hb : 0 ≤ b) (ha : 0 ≤ a)
    (hs : 2 * a / L + 1 + 2 * b / L < s) : b ≤ L / 2 * s ^ 2 - a * s := by
  have h1 : 2 * a / L * L = 2 * a := by field_simp
  have h2 : 2 * b / L * L = 2 * b := by field_simp
  have hs0 : 1 < s := by
    have : 0 ≤ 2 * a / L := by positivity
    have : 0 ≤ 2 * b / L := by positivity
    linarith
  have hLs : 2 * a + L + 2 * b < L * s := by nlinarith
  nlinarith

lemma Hyp.exists_xhat_min [ProperSpace E] (H : Hyp f gx gy L μx μy) (y : F) (z : E) :
    ∃ x, ∀ x', fhat f L z x y ≤ fhat f L z x' y := by
  apply exists_min_of_growth (fun x => fhat f L z x y)
    ((((H.continuous_x y).add (continuous_const.mul
      ((continuous_id.sub continuous_const).norm.pow 2))).lowerSemicontinuous)) z
    (2 * ‖gx z y‖ / L + 1 + 2 * 0 / L)
  intro x hx
  have h := H.fhat_lower z z x y
  simp only [sub_self, smul_zero, add_zero] at h
  have hg := growth_radius H.hL le_rfl (norm_nonneg (gx z y)) hx
  have hi : -(‖gx z y‖ * ‖x - z‖) ≤ ⟪gx z y, x - z⟫ := by
    have := abs_le.1 (abs_real_inner_le_norm (gx z y) (x - z)); linarith
  linarith

lemma Hyp.xhat_min [ProperSpace E] (H : Hyp f gx gy L μx μy) (y : F) (z x' : E) :
    psi f L y z ≤ fhat f L z x' y :=
  Classical.epsilon_spec (p := fun x => ∀ x', fhat f L z x y ≤ fhat f L z x' y)
    (H.exists_xhat_min y z) x'

lemma Hyp.xhat_grad [ProperSpace E] (H : Hyp f gx gy L μx μy) (y : F) (z : E) :
    gx (xhat f L y z) y + (2 * L) • (xhat f L y z - z) = 0 := by
  set x := xhat f L y z
  set h := gx x y + (2 * L) • (x - z)
  have hL := H.hL
  have h1 := H.fhat_upper z x (x - (1 / (3 * L)) • h) y
  have h2 := H.xhat_min y z (x - (1 / (3 * L)) • h)
  have he : x - (1 / (3 * L)) • h - x = -(1 / (3 * L)) • h := by abel_nf; simp [neg_smul]
  rw [he, inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs] at h1
  have : ‖h‖ ^ 2 ≤ 0 := by
    have hpsi : psi f L y z = fhat f L z x y := rfl
    have key : (-(1 / (3 * L)) + 3 * L / 2 * (-(1 / (3 * L))) ^ 2) * ‖h‖ ^ 2 ≥ 0 := by
      nlinarith
    have hc : -(1 / (3 * L)) + 3 * L / 2 * (-(1 / (3 * L))) ^ 2 = -(1 / (6 * L)) := by
      field_simp; ring
    rw [hc] at key
    have : 0 < 1 / (6 * L) := by positivity
    nlinarith
  have := norm_eq_zero.1 (by nlinarith [sq_nonneg ‖h‖, norm_nonneg h] : ‖h‖ = 0)
  exact this

lemma Hyp.psi_strong [ProperSpace E] (H : Hyp f gx gy L μx μy) (y : F) (z x' : E) :
    psi f L y z + L / 2 * ‖x' - xhat f L y z‖ ^ 2 ≤ fhat f L z x' y := by
  have h := H.fhat_lower z (xhat f L y z) x' y
  rw [H.xhat_grad y z, inner_zero_left, add_zero] at h
  exact h

lemma Hyp.fhat_sub_psi (H : Hyp f gx gy L μx μy) (z x : E) (y : F) :
    fhat f L z x y - psi f L y z ≤ ‖gx x y + (2 * L) • (x - z)‖ ^ 2 / (2 * L) := by
  set h := gx x y + (2 * L) • (x - z)
  have h1 := H.fhat_lower z x (xhat f L y z) y
  have hL := H.hL
  have hi : -(‖h‖ * ‖xhat f L y z - x‖) ≤ ⟪h, xhat f L y z - x⟫ := by
    have := abs_le.1 (abs_real_inner_le_norm h (xhat f L y z - x)); linarith
  have : fhat f L z x y - psi f L y z ≤ ‖h‖ * ‖xhat f L y z - x‖ - L / 2 * ‖xhat f L y z - x‖ ^ 2 := by
    simp only [psi]; linarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (‖h‖ - L * ‖xhat f L y z - x‖)]

lemma Hyp.dist_xhat [ProperSpace E] (H : Hyp f gx gy L μx μy) (z x : E) (y : F) :
    L * ‖x - xhat f L y z‖ ≤ ‖gx x y + (2 * L) • (x - z)‖ := by
  set h := gx x y + (2 * L) • (x - z)
  set d := ‖x - xhat f L y z‖
  have h1 := H.fhat_lower z x (xhat f L y z) y
  have h2 := H.psi_strong y z x
  have hL := H.hL
  have hi : ⟪h, xhat f L y z - x⟫ ≥ -(‖h‖ * d) := by
    have := abs_le.1 (abs_real_inner_le_norm h (xhat f L y z - x))
    rw [norm_sub_rev] at this; linarith
  have hn : ‖xhat f L y z - x‖ = d := norm_sub_rev _ _
  simp only [psi] at h2
  rw [hn] at h1
  have : L * d ^ 2 ≤ ‖h‖ * d := by nlinarith
  by_cases hd : d = 0
  · rw [hd, mul_zero]; exact norm_nonneg _
  · have hd' : 0 < d := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    nlinarith

lemma Hyp.psi_lower [ProperSpace E] (H : Hyp f gx gy L μx μy) (y y' : F) (z : E) :
    psi f L y z + ⟪gy (xhat f L y z) y, y' - y⟫ - L * ‖y' - y‖ ^ 2 ≤ psi f L y' z := by
  set x := xhat f L y' z
  set xh := xhat f L y z
  have h1 := H.lower_y x y y'
  have h2 := H.psi_strong y z x
  have hlip := H.lipy x xh y y
  simp only [sub_self, norm_zero, add_zero] at hlip
  have hi : ⟪gy x y - gy xh y, y' - y⟫ ≥ -(L * ‖x - xh‖ * ‖y' - y‖) := by
    have := abs_le.1 (abs_real_inner_le_norm (gy x y - gy xh y) (y' - y))
    nlinarith [norm_nonneg (y' - y)]
  have hpsi : psi f L y' z = f x y' + L * ‖x - z‖ ^ 2 := rfl
  have hf : fhat f L z x y = f x y + L * ‖x - z‖ ^ 2 := rfl
  rw [inner_sub_left] at hi
  have hL := H.hL
  nlinarith [sq_nonneg (‖x - xh‖ - ‖y' - y‖)]

lemma Hyp.xhat_lip [ProperSpace E] (H : Hyp f gx gy L μx μy) (y y' : F) (z z' : E) :
    ‖xhat f L y z - xhat f L y' z'‖ ≤ ‖y - y'‖ + 2 * ‖z - z'‖ := by
  set a := xhat f L y z
  set b := xhat f L y' z'
  have ha := H.xhat_grad y z
  have hb := H.xhat_grad y' z'
  have hL := H.hL
  have w1 := H.lower_x a b y
  have w2 := H.lower_x b a y
  have hmono : ⟪gx a y - gx b y, a - b⟫ ≥ -(L * ‖a - b‖ ^ 2) := by
    have e1 : ⟪gx a y, b - a⟫ = -⟪gx a y, a - b⟫ := by
      rw [← inner_neg_right, neg_sub]
    have e2 : ‖b - a‖ = ‖a - b‖ := norm_sub_rev _ _
    rw [e1, e2] at w1
    rw [inner_sub_left]
    linarith
  have hy := H.lipx b b y y'
  simp only [sub_self, norm_zero, zero_add] at hy
  have key : gx a y - gx b y + (gx b y - gx b y') + (2 * L) • (a - b) = (2 * L) • (z - z') := by
    have : gx a y + (2 * L) • (a - z) - (gx b y' + (2 * L) • (b - z')) = 0 := by
      rw [ha, hb, sub_zero]
    rw [← sub_eq_zero, ← this]
    simp only [smul_sub]; abel
  have hk := congrArg (fun v => ⟪v, a - b⟫) key
  simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hk
  have hc1 : ⟪gx b y - gx b y', a - b⟫ ≥ -(L * ‖y - y'‖ * ‖a - b‖) := by
    have := abs_le.1 (abs_real_inner_le_norm (gx b y - gx b y') (a - b))
    nlinarith [norm_nonneg (a - b)]
  have hc2 : ⟪z - z', a - b⟫ ≤ ‖z - z'‖ * ‖a - b‖ := real_inner_le_norm _ _
  have : L * ‖a - b‖ ^ 2 ≤ L * (‖y - y'‖ + 2 * ‖z - z'‖) * ‖a - b‖ := by nlinarith
  by_cases hd : ‖a - b‖ = 0
  · rw [hd]; positivity
  · have hd' : 0 < ‖a - b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    have : L * ‖a - b‖ ≤ L * (‖y - y'‖ + 2 * ‖z - z'‖) := by nlinarith
    exact le_of_mul_le_mul_left this hL

end Hat

section Envelope

variable {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μx μy : ℝ}

lemma Hyp.exists_xbar_min [ProperSpace E] (H : Hyp f gx gy L μx μy) (z : E) :
    ∃ x, ∀ x', phat f L z x ≤ phat f L z x' := by
  obtain ⟨y0⟩ : Nonempty F := ⟨0⟩
  have hb : 0 ≤ maxValue f z - f z y0 := by linarith [H.le_maxValue z y0]
  apply exists_min_of_growth (phat f L z)
    (H.lsc_maxValue.add (continuous_const.mul
      ((continuous_id.sub continuous_const).norm.pow 2)).lowerSemicontinuous) z
    (2 * ‖gx z y0‖ / L + 1 + 2 * (maxValue f z - f z y0) / L)
  intro x hx
  have h := H.fhat_lower z z x y0
  simp only [sub_self, smul_zero, add_zero] at h
  have hg := growth_radius H.hL hb (norm_nonneg (gx z y0)) hx
  have hi : -(‖gx z y0‖ * ‖x - z‖) ≤ ⟪gx z y0, x - z⟫ := by
    have := abs_le.1 (abs_real_inner_le_norm (gx z y0) (x - z)); linarith
  have hm := H.le_maxValue x y0
  simp only [phat, fhat, sub_self, norm_zero] at h ⊢
  nlinarith

lemma Hyp.xbar_min [ProperSpace E] (H : Hyp f gx gy L μx μy) (z x' : E) :
    envelope f L z ≤ phat f L z x' :=
  Classical.epsilon_spec (p := fun x => ∀ x', phat f L z x ≤ phat f L z x')
    (H.exists_xbar_min z) x'

lemma Hyp.fhat_mid (H : Hyp f gx gy L μx μy) (z a b : E) (y : F) :
    fhat f L z ((1 / 2 : ℝ) • (a + b)) y ≤
      (fhat f L z a y + fhat f L z b y) / 2 - L / 8 * ‖a - b‖ ^ 2 := by
  set m := (1 / 2 : ℝ) • (a + b)
  have h1 := H.fhat_lower z m a y
  have h2 := H.fhat_lower z m b y
  have ea : a - m = (1 / 2 : ℝ) • (a - b) := by simp only [m]; module
  have eb : b - m = -((1 / 2 : ℝ) • (a - b)) := by simp only [m]; module
  rw [ea] at h1
  rw [eb, inner_neg_right, norm_neg] at h2
  rw [norm_smul] at h1 h2
  norm_num at h1 h2
  nlinarith

lemma Hyp.phat_mid (H : Hyp f gx gy L μx μy) (z a b : E) :
    phat f L z ((1 / 2 : ℝ) • (a + b)) ≤
      (phat f L z a + phat f L z b) / 2 - L / 8 * ‖a - b‖ ^ 2 := by
  obtain ⟨y, hy⟩ := H.maxValue_attained ((1 / 2 : ℝ) • (a + b))
  have h := H.fhat_mid z a b y
  have ha := H.le_maxValue a y
  have hb := H.le_maxValue b y
  simp only [phat, fhat] at h ⊢
  rw [hy]
  linarith

lemma Hyp.envelope_strong [ProperSpace E] (H : Hyp f gx gy L μx μy) (z x' : E) :
    envelope f L z + L / 4 * ‖x' - xbar f L z‖ ^ 2 ≤ phat f L z x' := by
  have h := H.phat_mid z (xbar f L z) x'
  have hm := H.xbar_min z ((1 / 2 : ℝ) • (xbar f L z + x'))
  have hn : ‖xbar f L z - x'‖ = ‖x' - xbar f L z‖ := norm_sub_rev _ _
  simp only [envelope] at hm ⊢
  rw [hn] at h
  linarith

lemma Hyp.psi_le_envelope [ProperSpace E] (H : Hyp f gx gy L μx μy) (y : F) (z : E) :
    psi f L y z ≤ envelope f L z := by
  have h := H.xhat_min y z (xbar f L z)
  have hm := H.le_maxValue (xbar f L z) y
  simp only [envelope, phat, fhat] at h ⊢
  linarith

lemma Hyp.minimax_le_envelope (H : Hyp f gx gy L μx μy) (z : E) :
    minimaxValue f ≤ envelope f L z := by
  have := H.minimax_le (xbar f L z)
  simp only [envelope, phat]
  nlinarith [sq_nonneg ‖xbar f L z - z‖, H.hL]

lemma Hyp.envelope_sub_psi [ProperSpace E] (H : Hyp f gx gy L μx μy) (y : F) (z : E) :
    2 * μy * (envelope f L z - psi f L y z) ≤ ‖gy (xhat f L y z) y‖ ^ 2 := by
  set x := xhat f L y z
  have h1 := H.maxValue_sub_le x y
  have h2 := H.xbar_min z x
  have hμ := H.hμy
  have : envelope f L z - psi f L y z ≤ maxValue f x - f x y := by
    simp only [psi, phat, fhat] at h2 ⊢; linarith
  rw [le_div_iff₀ (by linarith)] at h1
  nlinarith

lemma Hyp.xhat_sub_xbar [ProperSpace E] (H : Hyp f gx gy L μx μy) (y : F) (z : E) :
    L * μy * ‖xhat f L y z - xbar f L z‖ ^ 2 ≤ 2 * ‖gy (xhat f L y z) y‖ ^ 2 := by
  set x := xhat f L y z
  have h1 := H.maxValue_sub_le x y
  have h2 := H.envelope_strong z x
  have h3 := H.psi_le_envelope y z
  have hμ := H.hμy
  have : L / 4 * ‖x - xbar f L z‖ ^ 2 ≤ maxValue f x - f x y := by
    simp only [psi, phat, fhat] at h2 h3 ⊢; linarith
  rw [le_div_iff₀ (by linarith)] at h1
  nlinarith

lemma Hyp.envelope_gap [ProperSpace E] (H : Hyp f gx gy L μx μy) (y : F) (z : E) :
    envelope f L z - minimaxValue f ≤
      (envelope f L z - psi f L y z) + (L + 2 * L ^ 2 / μx) * ‖xhat f L y z - z‖ ^ 2 := by
  set x := xhat f L y z
  have h1 := H.sub_minimax_le x y
  have hg : gx x y = -((2 * L) • (x - z)) := eq_neg_of_add_eq_zero_left (H.xhat_grad y z)
  rw [hg, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [H.hL]), mul_pow] at h1
  have hμ := H.hμx
  have e : (2 * L) ^ 2 * ‖x - z‖ ^ 2 / (2 * μx) = 2 * L ^ 2 / μx * ‖x - z‖ ^ 2 := by
    field_simp
  rw [e] at h1
  have hpsi : psi f L y z = f x y + L * ‖x - z‖ ^ 2 := rfl
  linarith

end Envelope

end OracleTemplate.TwoSidedPL
