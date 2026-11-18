import LongTails.Proofs.DuelingReferenceDrift
import LongTails.Proofs.ZerothOrderSmoothing

open MeasureTheory
open scoped RealInnerProductSpace
open LongTails.Setups.StronglyConvexDueling
open LongTails.Algorithms.DuelingReferenceDescent
open LongTails.Proofs.DuelingReferenceDrift

namespace LongTails.Proofs.DuelingReferenceSmoothing

noncomputable def mean3 (F : Fin 3 → ℝ) : ℝ := (F 1 + F 2 + F 0) / 3

noncomputable def value {p : Params} (f : Point p.d → ℝ) (ρ : ℝ → ℝ)
    (x y : Point p.d) : ℝ := mean3 (fun i => ρ (f y - f (anchor p x i)))

noncomputable def weight {p : Params} (f : Point p.d → ℝ) (ρ : ℝ → ℝ)
    (x y : Point p.d) : ℝ := mean3 (fun i => deriv ρ (f y - f (anchor p x i)))

lemma value_gradient {p : Params} {f : Point p.d → ℝ} {ρ : ℝ → ℝ}
    (hf : Objective p f) (hr : Transfer p ρ) (x y : Point p.d) :
    HasGradientAt (value (p := p) f ρ x) ((weight (p := p) f ρ x y) • gradient f y) y := by
  let v := fun i : Fin 3 => f (anchor p x i)
  have h (i : Fin 3) := (hr.differentiable (f y - v i)).comp_hasFDerivAt y
    ((hf.differentiable y).hasFDerivAt.sub_const (v i))
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (((h 1).add (h 2)).add (h 0)).const_mul (1/3:ℝ) using 1
  · funext z
    simp [value, mean3, v, Function.comp_def]
    ring
  · ext z
    simp [weight, mean3, v]
    ring

lemma spacing_bounds {p : Params} (hr : 0 < p.r) :
    0 < spacing p ∧ spacing p ≤ 1 ∧ 8 * p.G * spacing p ≤ p.r := by
  unfold spacing
  have hpos : 0 < max 1 (8 * p.G / p.r) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨one_div_pos.mpr hpos, (div_le_iff₀ hpos).2 (by simp), ?_⟩
  rw [mul_one_div, div_le_iff₀ hpos]
  have := (div_le_iff₀ hr).mp (le_max_right 1 (8*p.G/p.r))
  linarith

lemma anchor_bounds {p : Params} {x : Point p.d} (hx : x ∈ Ball p.d)
    (hs : 0 < spacing p) (hs' : spacing p ≤ 1) (i : Fin 3) :
    anchor p x i ∈ Ball p.d ∧ ‖anchor p x i - x‖ ≤ 2 * spacing p := by
  have hh (v : Point p.d) (hv : ‖v‖ ≤ 1) := And.intro
    (convex_ball hx (mem_ball hv) hs.le hs') (perturb_dist hx (mem_ball hv) hs.le)
  fin_cases i
  · simpa [anchor] using hh 0 (by simp)
  · simpa [anchor] using hh (axis p.d) (axis_unit p).le
  · simpa [anchor, sub_eq_add_neg] using hh (-(axis p.d)) (by rw [norm_neg,axis_unit])

lemma weight_bounds {p : Params} {f : Point p.d → ℝ} {ρ : ℝ → ℝ}
    (hp : spec.valid p) (hf : Objective p f) (hr : Transfer p ρ) {x y : Point p.d}
    (hx : x ∈ Ball p.d) (hy : y ∈ Ball p.d) (hd : ‖y-x‖ ≤ 2 * spacing p) :
    slope p ≤ weight (p := p) f ρ x y ∧ weight (p := p) f ρ x y ≤ p.M := by
  obtain ⟨hμ, _, hG, hrad, hc, _, _⟩ := hp
  obtain ⟨hs, hs', hsr⟩ := spacing_bounds hrad
  have ha := anchor_bounds hx hs hs'
  have hg (i : Fin 3) : |f y - f (anchor p x i)| ≤ p.r := by
    apply (hf.lipschitz y hy _ (ha i).1).trans
    have hdist := norm_sub_le_norm_sub_add_norm_sub y x (anchor p x i)
    rw [norm_sub_rev x (anchor p x i)] at hdist
    have ht : ‖y - anchor p x i‖ ≤ 4 * spacing p := by linarith [hdist,(ha i).2]
    nlinarith [mul_le_mul_of_nonneg_left ht hG.le, mul_pos hG hs]
  refine ⟨anchor_gain hf hr hc.le hμ.le (fun i => (ha i).1) hg, ?_⟩
  unfold weight mean3
  linarith [hr.slope_upper _ (hg 0), hr.slope_upper _ (hg 1), hr.slope_upper _ (hg 2)]

end LongTails.Proofs.DuelingReferenceSmoothing
