import LongTails.Algorithms.DuelingReferenceDescent
import LongTails.Proofs.DuelingReferenceGeometry

open MeasureTheory
open scoped RealInnerProductSpace
open LongTails.Setups.StronglyConvexDueling
open LongTails.Algorithms.DuelingReferenceDescent

namespace LongTails.Proofs.DuelingReferenceDrift

lemma norm_ball {d : ℕ} {x : Point d} (hx : x ∈ Ball d) : ‖x‖ ≤ 1 := by
  simpa [Ball, Metric.mem_closedBall] using hx

lemma mem_ball {d : ℕ} {x : Point d} (hx : ‖x‖ ≤ 1) : x ∈ Ball d := by
  simpa [Ball, Metric.mem_closedBall] using hx

lemma retract_eq {d : ℕ} {x : Point d} (hx : x ∈ Ball d) : (retract x : Point d) = x :=
  OracleTemplate.clip_eq_self (norm_ball hx)

lemma axis_unit (p : Params) : ‖axis p.d‖ = 1 :=
  (EuclideanSpace.basisFun (Fin p.d) ℝ).orthonormal.norm_eq_one 0

lemma convex_ball {d : ℕ} {x y : Point d} (hx : x ∈ Ball d) (hy : y ∈ Ball d)
    {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) : (1-s) • x + s • y ∈ Ball d :=
  (convex_closedBall (0 : Point d) 1) hx hy (sub_nonneg.mpr hs') hs (by ring)

lemma perturb_dist {d : ℕ} {x y : Point d} (hx : x ∈ Ball d) (hy : y ∈ Ball d)
    {s : ℝ} (hs : 0 ≤ s) : ‖(1-s) • x + s • y - x‖ ≤ 2*s := by
  rw [show (1-s) • x + s • y - x = s • (y-x) by module, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hs]
  have hd : ‖y-x‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [norm_ball hx, norm_ball hy])
  nlinarith [mul_le_mul_of_nonneg_left hd hs]

lemma anchor_gain {p : Params} {f : Point p.d → ℝ} {ρ : ℝ → ℝ} (hf : Objective p f) (hρ : Transfer p ρ)
    (hc : 0 ≤ p.c) (hμ : 0 ≤ p.μ) {x y : Point p.d}
    (hin : ∀ j, anchor p x j ∈ Ball p.d)
    (hlocal : ∀ j, |f y - f (anchor p x j)| ≤ p.r) :
    slope p ≤ (deriv ρ (f y - f (anchor p x 1)) + deriv ρ (f y - f (anchor p x 2)) +
      deriv ρ (f y - f (anchor p x 0))) / 3 := by
  let z := (1 - spacing p) • x
  have h0 : anchor p x 0 = z := by simp [anchor, z]
  have h1 : anchor p x 1 = z + spacing p • axis p.d := by norm_num [anchor, z]
  have h2 : anchor p x 2 = z - spacing p • axis p.d := by norm_num [anchor, z]
  have hm := hf.strongly_convex _ (hin 0) _ (hin 2)
  have hp := hf.strongly_convex _ (hin 0) _ (hin 1)
  rw [h0,h2] at hm
  rw [h0,h1] at hp
  rw [add_sub_cancel_left] at hp
  rw [show z - spacing p • axis p.d - z = -(spacing p • axis p.d) by abel] at hm
  have hh := DuelingReferenceGeometry.chord_curvature (axis_unit p) hp hm
  apply DuelingReferenceGeometry.reference_slope _ (by positivity) hc
    (hρ.slope_lower _ (hlocal 1)) (hρ.slope_lower _ (hlocal 2)) (hρ.slope_lower _ (hlocal 0))
  rw [h0, h1, h2]
  linarith

end LongTails.Proofs.DuelingReferenceDrift
