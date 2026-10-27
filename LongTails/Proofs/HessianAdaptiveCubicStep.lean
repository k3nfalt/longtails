import LongTails.Proofs.HessianAdaptiveCubicModel
import LongTails.Proofs.AdaptiveCubicEnergy
import LongTails.Proofs.HessianAdaptiveCubicInvariants
import LongTails.Proofs.GdConvex
import LongTails.Proofs.HessianAdaptiveCubicNormalization

open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.HessianAdaptiveCubicStep

lemma contracting_linearization {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (w u x g : E)
    (A a α : ℝ) (hA : 0 ≤ A) (ha : 0 < a) (hα : 0 < α) (hαone : α ≤ 1)
    (hcap : a ≤ α * (A + a))
    (hsupport : ∀ z, f ((1 - α) • w + α • u) +
      ⟪g, z - ((1 - α) • w + α • u)⟫ ≤ f z) :
    (A + a) * (f ((A + a)⁻¹ • (A • w + a • u)) - f x) -
      A * (f w - f x) ≤ a * ⟪g, u - x⟫ := by
  let y := (1 - α) • w + α • u
  let b := a / (α * (A + a))
  have hsum : 0 < A + a := by positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hbone : b ≤ 1 := (div_le_one (mul_pos hα hsum)).2 hcap
  have hmix : (A + a)⁻¹ • (A • w + a • u) = (1 - b) • w + b • y := by
    have hc1 : (A + a)⁻¹ * A = 1 - b * α := by
      dsimp [b]
      field_simp
      ring
    have hc2 : (A + a)⁻¹ * a = b * α := by
      dsimp [b]
      field_simp
    dsimp only [y]
    simp only [smul_add, smul_smul]
    rw [hc1, hc2]
    module
  have hconv := hf.2 (Set.mem_univ w) (Set.mem_univ y)
    (sub_nonneg.mpr hbone) hb (by ring : 1 - b + b = 1)
  rw [← hmix] at hconv
  have hscaled := mul_le_mul_of_nonneg_left hconv hsum.le
  have hsw := hsupport w
  have hsx := hsupport x
  have hiw : ⟪g, w - ((1 - α) • w + α • u)⟫ =
      α * (⟪g, w⟫ - ⟪g, u⟫) := by simp only [inner_sub_right,
        inner_add_right, real_inner_smul_right]; ring
  have hix : ⟪g, x - ((1 - α) • w + α • u)⟫ =
      ⟪g, x⟫ - (1 - α) * ⟪g, w⟫ - α * ⟪g, u⟫ := by
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right]; ring
  rw [hiw] at hsw
  rw [hix] at hsx
  have hweighted := mul_le_mul_of_nonneg_left hsw (sub_nonneg.mpr hαone)
  have hweightedx := mul_le_mul_of_nonneg_left hsx hα.le
  have hid : (A + a) * b = a / α := by dsimp [b]; field_simp
  have he : α * ((A + a) * (f ((A + a)⁻¹ • (A • w + a • u)) - f x) -
      A * (f w - f x) - a * ⟪g, u - x⟫) ≤ 0 := by
    simp only [inner_sub_right]
    dsimp only [y] at hscaled
    have hscale := mul_le_mul_of_nonneg_left hscaled hα.le
    have hid' : α * ((A + a) * b) = a := by rw [hid]; field_simp
    simp only [smul_eq_mul] at hscale
    have hcoeff : α * ((A + a) * ((1 - b) * f w + b * f ((1 - α) • w + α • u))) =
        (α * (A + a) - a) * f w + a * f ((1 - α) • w + α • u) := by
      linear_combination (f ((1 - α) • w + α • u) - f w) * hid'
    rw [hcoeff] at hscale
    have hw := mul_le_mul_of_nonneg_left hweighted ha.le
    have hx := mul_le_mul_of_nonneg_left hweightedx ha.le
    nlinarith
  nlinarith

lemma optimizer_pair_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v z x g r : E) (a c κ : ℝ)
    (hprimal : a * ⟪g - r, u - v⟫ ≤ -c * ⟪u - z, u - v⟫)
    (hdual : a * ⟪g, v - x⟫ ≤ κ * ⟪z - v, v - x⟫) :
    a * ⟪g, u - x⟫ + κ / 2 * ‖v - x‖ ^ 2 - κ / 2 * ‖z - x‖ ^ 2 ≤
      a * ⟪r, (u - z) - (v - z)⟫ - c * ⟪u - z, (u - z) - (v - z)⟫ -
        κ / 2 * ‖v - z‖ ^ 2 := by
  have hsplit : ⟪g, u - x⟫ = ⟪g, u - v⟫ + ⟪g, v - x⟫ := by
    simp only [inner_sub_right]; ring
  have hid : (u - z) - (v - z) = u - v := by abel
  have hnorm : ‖z - x‖ ^ 2 = ‖v - x‖ ^ 2 + ‖v - z‖ ^ 2 +
      2 * ⟪z - v, v - x⟫ := by
    have he : z - x = (z - v) + (v - x) := by abel
    rw [he, norm_add_sq_real, norm_sub_rev z v]
    ring
  rw [hid, hsplit, hnorm]
  rw [inner_sub_left] at hprimal
  nlinarith

lemma optimizer_energy_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v z x g r : E) (a c κ D : ℝ) (ha : 0 ≤ a) (hc : 0 < c) (hκ : c ≤ κ)
    (hdiam : ‖u - v‖ ≤ D)
    (hprimal : a * ⟪g - r, u - v⟫ ≤ -c * ⟪u - z, u - v⟫)
    (hdual : a * ⟪g, v - x⟫ ≤ κ * ⟪z - v, v - x⟫) :
    a * ⟪g, u - x⟫ + κ / 2 * ‖v - x‖ ^ 2 - κ / 2 * ‖z - x‖ ^ 2 +
      c / 2 * ‖u - z‖ ^ 2 ≤ min (a ^ 2 / c * ‖r‖ ^ 2) (a * D * ‖r‖) := by
  have hp := optimizer_pair_bound u v z x g r a c κ hprimal hdual
  have hsq := AdaptiveCubicEnergy.optimistic_square (a := a) hc hκ r (u - z) (v - z)
  have hnorm : ‖(u - z) - (v - z)‖ ≤ D := by
    have he : (u - z) - (v - z) = u - v := by abel
    simpa only [he] using hdiam
  have hlin := AdaptiveCubicEnergy.optimistic_linear ha hc hκ r (u - z) (v - z) hnorm
  apply le_min
  · have hid : c * (a ^ 2 / c * ‖r‖ ^ 2) = a ^ 2 * ‖r‖ ^ 2 := by field_simp
    have hpos := mul_nonneg (sq_nonneg a) (sq_nonneg ‖r‖)
    nlinarith
  · linarith

lemma contracting_energy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (w u v z x g r e : E)
    (A a α c κ D : ℝ) (hA : 0 ≤ A) (ha : 0 < a) (hα : 0 < α) (hαone : α ≤ 1)
    (hcap : a ≤ α * (A + a)) (hc : 0 < c) (hκ : c ≤ κ) (hdiam : ‖u - v‖ ≤ D)
    (hsupport : ∀ q, f ((1 - α) • w + α • u) +
      ⟪g - e, q - ((1 - α) • w + α • u)⟫ ≤ f q)
    (hprimal : a * ⟪g - r, u - v⟫ ≤ -c * ⟪u - z, u - v⟫)
    (hdual : a * ⟪g, v - x⟫ ≤ κ * ⟪z - v, v - x⟫) :
    (A + a) * (f ((A + a)⁻¹ • (A • w + a • u)) - f x) +
      κ / 2 * ‖v - x‖ ^ 2 + c / 2 * ‖u - z‖ ^ 2 ≤
    A * (f w - f x) + κ / 2 * ‖z - x‖ ^ 2 +
      min (a ^ 2 / c * ‖r‖ ^ 2) (a * D * ‖r‖) - a * ⟪e, u - x⟫ := by
  have hlin := contracting_linearization hf w u x (g - e) A a α hA ha hα hαone hcap hsupport
  have hopt := optimizer_energy_bound u v z x g r a c κ D ha.le hc hκ hdiam hprimal hdual
  rw [inner_sub_left] at hlin
  linarith

lemma scale_primal_variational {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v z g r : E) (a q : ℝ) (ha : 0 ≤ a)
    (hvi : 0 ≤ ⟪g - r + q • (u - z), v - u⟫) :
    a * ⟪g - r, u - v⟫ ≤ -(a * q) * ⟪u - z, u - v⟫ := by
  have hvu : v - u = -(u - v) := by abel
  rw [hvu, inner_neg_right, inner_add_left, real_inner_smul_left] at hvi
  have h := mul_nonneg ha hvi
  nlinarith

lemma scale_dual_variational {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v z x g : E) (a q : ℝ) (ha : 0 ≤ a)
    (hvi : 0 ≤ ⟪g + q • (v - z), x - v⟫) :
    a * ⟪g, v - x⟫ ≤ (a * q) * ⟪z - v, v - x⟫ := by
  have hxv : x - v = -(v - x) := by abel
  have hzv : z - v = -(v - z) := by abel
  rw [hxv, inner_neg_right, inner_add_left, real_inner_smul_left] at hvi
  rw [hzv, inner_neg_left]
  have h := mul_nonneg ha hvi
  nlinarith

open LongTails.Setups.HessianAdaptiveStochasticConvex
open LongTails.Algorithms.HessianAdaptiveCubic
open LongTails.Proofs.HessianAdaptiveCubicModel
open LongTails.Proofs.HessianAdaptiveCubicWeights
open LongTails.Proofs.HessianAdaptiveCubicInvariants

lemma primal_certificate (p : Public) (s : State p.d) (gd : Point p.d)
    (hD : 0 < p.D) (hs : Invariant p s) (hH : IsPSD s.modelHessian)
    (htrial : s.trial = primal p s s.modelHessian) (v : Point p.d) (hv : v ∈ p.C) :
    increment p s * ⟪gd - (gd - s.modelGradient - s.modelHessian (displacement s)), s.trial - v⟫ ≤
      -(increment p s * (mixing s.iteration * damping p s)) * ⟪s.trial - s.dual, s.trial - v⟫ := by
  have ha := increment_pos p s hD hs.scale hs.iteration hs.weight_pos
  have hraw : ∀ x ∈ p.C, 0 ≤ ⟪s.modelGradient + s.modelHessian (displacement s) +
      (mixing s.iteration * damping p s) • (s.trial - s.dual), x - s.trial⟫ := by
    dsimp only [displacement, damping]
    rw [htrial]
    exact primal_variational p.C p.x0 s.dual s.modelGradient s.modelHessian
      (mixing s.iteration) (quadraticDamping p s) s.scale (mixing_pos _).le hH
  have he : gd - (gd - s.modelGradient - s.modelHessian (displacement s)) =
      s.modelGradient + s.modelHessian (displacement s) := by abel
  apply scale_primal_variational _ _ _ _ _ _ _ ha.le
  rw [he]
  exact hraw v hv

lemma dual_certificate (p : Public) (s : State p.d) (gd xstar : Point p.d)
    (hD : 0 < p.D) (hs : Invariant p s) (hx : xstar ∈ p.C) :
    increment p s * ⟪gd, (advance p s gd).dual - xstar⟫ ≤
      s.scale * ⟪s.dual - (advance p s gd).dual, (advance p s gd).dual - xstar⟫ := by
  have ha := increment_pos p s hD hs.scale hs.iteration hs.weight_pos
  have hv := dual_variational p.C p.x0 s.dual gd s.scale (increment p s) xstar hx
  have hscaled := scale_dual_variational _ s.dual xstar gd (increment p s)
    (s.scale / increment p s) ha.le hv
  have he : increment p s * (s.scale / increment p s) = s.scale := by field_simp
  rw [he] at hscaled
  exact hscaled

def energy (p : Public) (f : Point p.d → ℝ) (xstar : Point p.d) (s : State p.d) : ℝ :=
  s.weight * (f s.point - f xstar) + s.scale / 2 * ‖s.dual - xstar‖ ^ 2

def movement (p : Public) (s : State p.d) : ℝ :=
  (increment p s * mixing s.iteration * damping p s / s.scale) * ‖s.trial - s.dual‖ ^ 2

lemma energy_nonneg (p : Public) (f : Point p.d → ℝ) (xstar : Point p.d) (s : State p.d)
    (hs : Invariant p s) (hmin : IsMinOn f p.C xstar) : 0 ≤ energy p f xstar s := by
  have hgap : 0 ≤ f s.point - f xstar := sub_nonneg.mpr (hmin hs.point)
  have hweight := hs.weight
  have hscale := hs.scale
  unfold energy
  positivity

lemma movement_bounds (p : Public) (s : State p.d) (hD : 0 < p.D) (hs : Invariant p s)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D) :
    0 ≤ movement p s ∧ movement p s ≤ p.D ^ 2 := by
  exact normalized_movement_cap
    (increment_pos p s hD hs.scale hs.iteration hs.weight_pos).le (mixing_pos _).le
    (damping_pos p s hD hs.scale hs.iteration).le hs.scale (norm_nonneg _)
    (hdiam _ hs.trial _ hs.dual) (increment_damping_cap p s hD hs.scale hs.iteration)

lemma model_step_energy (p : Public) (s : State p.d) (gd xstar : Point p.d)
    (f : Point p.d → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hD : 0 < p.D) (hs : Invariant p s) (hx : xstar ∈ p.C)
    (hH : IsPSD s.modelHessian) (htrial : s.trial = primal p s s.modelHessian)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D) :
    let a := increment p s
    let c := a * (mixing s.iteration * damping p s)
    let r := gd - s.modelGradient - s.modelHessian (displacement s)
    (s.weight + a) * (f (advance p s gd).point - f xstar) +
      s.scale / 2 * ‖(advance p s gd).dual - xstar‖ ^ 2 + c / 2 * ‖s.trial - s.dual‖ ^ 2 ≤
    energy p f xstar s + min (a ^ 2 / c * ‖r‖ ^ 2) (a * p.D * ‖r‖) -
      a * ⟪gd - gradient f (queryPoint s), s.trial - xstar⟫ := by
  have ha := increment_pos p s hD hs.scale hs.iteration hs.weight_pos
  have hα := mixing_pos s.iteration
  have hτ := damping_pos p s hD hs.scale hs.iteration
  have hc : 0 < increment p s * (mixing s.iteration * damping p s) := by positivity
  have hv : (advance p s gd).dual ∈ p.C := (model_minimize_spec p.C p.x0 _ _ _ _ _).1
  have hsupport : ∀ q, f ((1 - mixing s.iteration) • s.point + mixing s.iteration • s.trial) +
      ⟪gd - (gd - gradient f (queryPoint s)),
        q - ((1 - mixing s.iteration) • s.point + mixing s.iteration • s.trial)⟫ ≤ f q := by
    intro q
    have hg := OracleTemplate.Gradient.convex_support hf hgrad (queryPoint s) q
    rw [queryPoint_eq] at hg ⊢
    simp only [sub_sub_cancel]
    linarith
  exact contracting_energy hf s.point s.trial (advance p s gd).dual s.dual xstar gd
    (gd - s.modelGradient - s.modelHessian (displacement s))
    (gd - gradient f (queryPoint s)) s.weight (increment p s) (mixing s.iteration)
    (increment p s * (mixing s.iteration * damping p s)) s.scale p.D hs.weight ha hα
    (mixing_le_one hs.iteration) (increment_weight_cap p s hs.iteration hs.weight)
    hc (increment_damping_cap p s hD hs.scale hs.iteration) (hdiam _ hs.trial _ hv)
    hsupport (primal_certificate p s gd hD hs hH htrial _ hv)
    (dual_certificate p s gd xstar hD hs hx)

lemma adaptive_step_energy (p : Public) (s : State p.d) (gd xstar : Point p.d)
    (f : Point p.d → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hD : 0 < p.D) (hs : Invariant p s) (hx : xstar ∈ p.C)
    (hH : IsPSD s.modelHessian) (htrial : s.trial = primal p s s.modelHessian)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D) :
    energy p f xstar (advance p s gd) + s.scale / 2 * movement p s ≤
      energy p f xstar s + (7 / 2) * p.D ^ 2 * ((advance p s gd).scale - s.scale) -
        increment p s * ⟪gd - gradient f (queryPoint s), s.trial - xstar⟫ := by
  let a := increment p s
  let c := a * (mixing s.iteration * damping p s)
  let r := gd - s.modelGradient - s.modelHessian (displacement s)
  let R := Real.sqrt (s.scale ^ 2 + residualWeight p s * ‖r‖ ^ 2 / p.D ^ 2)
  let Λ := (advance p s gd).scale
  let v := (advance p s gd).dual
  let G := f (advance p s gd).point - f xstar
  have ha : 0 < a := increment_pos p s hD hs.scale hs.iteration hs.weight_pos
  have hα := mixing_pos s.iteration
  have hτ := damping_pos p s hD hs.scale hs.iteration
  have hκ := hs.scale
  have hc : 0 < c := by dsimp [c]; positivity
  have hcκ : c ≤ s.scale := increment_damping_cap p s hD hs.scale hs.iteration
  have hW := residualWeight_nonneg p s hD hs
  have hrad : 0 ≤ s.scale ^ 2 + residualWeight p s * ‖r‖ ^ 2 / p.D ^ 2 := by positivity
  have hR : s.scale ≤ R := by
    apply (Real.le_sqrt hκ.le hrad).2
    nlinarith [div_nonneg (mul_nonneg hW (sq_nonneg ‖r‖)) (sq_nonneg p.D)]
  have hsq : (R ^ 2 - s.scale ^ 2) * (c * p.D ^ 2) = s.scale * a ^ 2 * ‖r‖ ^ 2 := by
    rw [show R ^ 2 = s.scale ^ 2 + residualWeight p s * ‖r‖ ^ 2 / p.D ^ 2 from Real.sq_sqrt hrad]
    dsimp [c, a, residualWeight]
    field_simp
    ring
  have hΛ : R ≤ Λ := le_max_left _ _
  have hv : v ∈ p.C := (model_minimize_spec p.C p.x0 _ _ _ _ _).1
  have hdist : ‖v - xstar‖ ^ 2 ≤ p.D ^ 2 := by
    have h := hdiam v hv xstar hx
    nlinarith [norm_nonneg (v - xstar)]
  have hraw := model_step_energy p s gd xstar f hf hgrad hD hs hx hH htrial hdiam
  have hraw' : (s.weight + a) * G + s.scale / 2 * ‖v - xstar‖ ^ 2 +
      c / 2 * ‖s.trial - s.dual‖ ^ 2 ≤ energy p f xstar s +
      min (a ^ 2 / c * ‖r‖ ^ 2) (a * p.D * ‖r‖) +
      (-a * ⟪gd - gradient f (queryPoint s), s.trial - xstar⟫) := by
    simpa only [a, c, r, G, v, neg_mul, sub_eq_add_neg] using hraw
  have hscaled := AdaptiveCubicEnergy.adaptive_scale_energy hκ hR hΛ hc hcκ hD hdist hsq hraw'
  have hmove : s.scale * movement p s = c * ‖s.trial - s.dual‖ ^ 2 := by
    dsimp [movement, c, a]
    field_simp
  change (s.weight + a) * G + Λ / 2 * ‖v - xstar‖ ^ 2 + s.scale / 2 * movement p s ≤ _
  change _ ≤ energy p f xstar s + (7 / 2) * p.D ^ 2 * (Λ - s.scale) -
    a * ⟪gd - gradient f (queryPoint s), s.trial - xstar⟫
  nlinarith

lemma residual_movement_caps (p : Public) (s : State p.d) (hD : 0 < p.D)
    (hs : Invariant p s) :
    residualWeight p s * ‖displacement s‖ ^ 2 ≤ (s.iteration : ℝ) ^ 2 ∧
      residualWeight p s * ‖displacement s‖ ^ 4 ≤ movement p s := by
  have hα := mixing_pos s.iteration
  have hτ := damping_pos p s hD hs.scale hs.iteration
  have ha := increment_pos p s hD hs.scale hs.iteration hs.weight_pos
  have hβ := quadraticDamping_pos p s hD hs.scale hs.iteration
  have hdamp : s.scale * ‖displacement s‖ ≤ damping p s := by
    unfold damping
    linarith
  have hc := scalar_residual_weight_caps ha.le hα hτ hs.scale
    (norm_nonneg (displacement s)) (increment_damping_cap p s hD hs.scale hs.iteration) hdamp
  have hid : (increment p s * damping p s / (mixing s.iteration * s.scale)) *
      ‖displacement s‖ ^ 2 = movement p s := by
    rw [displacement, norm_smul, Real.norm_eq_abs, abs_of_pos hα]
    unfold movement
    field_simp
  constructor
  · apply hc.1.trans
    have h := mul_self_le_mul_self (inv_nonneg.mpr hα.le) (mixing_inverse_le hs.iteration)
    simpa only [← sq, ← inv_pow, one_div] using h
  · exact hc.2.trans_eq hid

lemma normalized_step_energy (p : Public) (s : State p.d) (gd xstar : Point p.d)
    (f : Point p.d → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hD : 0 < p.D) (hs : Invariant p s) (hx : xstar ∈ p.C)
    (hmin : IsMinOn f p.C xstar) (hH : IsPSD s.modelHessian)
    (htrial : s.trial = primal p s s.modelHessian)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D) :
    energy p f xstar (advance p s gd) / (advance p s gd).scale +
      (s.scale / (advance p s gd).scale) / 2 * movement p s ≤
    energy p f xstar s / s.scale + (7 / 2) * p.D ^ 2 *
      (1 - s.scale / (advance p s gd).scale) +
      (-increment p s * ⟪gd - gradient f (queryPoint s), s.trial - xstar⟫) /
        (advance p s gd).scale := by
  apply HessianAdaptiveCubicNormalization.normalized_energy_step hs.scale
    (advance_scale_ge p s gd hD hs) (energy_nonneg p f xstar s hs hmin)
  simpa only [neg_mul, sub_eq_add_neg] using
    adaptive_step_energy p s gd xstar f hf hgrad hD hs hx hH htrial hdiam

end LongTails.Proofs.HessianAdaptiveCubicStep
