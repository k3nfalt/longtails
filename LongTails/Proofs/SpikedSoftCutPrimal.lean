import LongTails.Proofs.SpikedSoftCutCoordinates
import LongTails.Proofs.SoftCutCertificate
import Mathlib.Analysis.Convex.Jensen

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SpikedSoftCutPrimal

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCut
open LongTails.Proofs.SpikedSoftCutCoordinates

lemma join_weighted_sum (q : Params) {T : ℕ} (w : Fin T → ℝ)
    (hwsum : ∑ i, w i = 1) (a : ℝ) (x : Fin T → InnerSpace q) :
    join q a (∑ i, w i • x i) = ∑ i, w i • join q a (x i) := by
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [join, ← Finset.sum_mul, hwsum]
  · simp [join]

lemma weighted_primal_certificate (q : Params) {T : ℕ}
    (f : Space q → ℝ) (v : Space q → Space q)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hsupport : ∀ x y, ⟪v x, y-x⟫ ≤ f y-f x)
    (w : Fin T → ℝ) (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (a astar δ : ℝ) (x : Fin T → InnerSpace q) (ystar : InnerSpace q)
    (hcertificate : ∑ i, w i * ⟪tail q (v (join q a (x i))), x i-ystar⟫ ≤ δ) :
    f (join q a (∑ i, w i • x i)) - f (join q astar ystar) +
      (∑ i, w i * head q (v (join q a (x i)))) * (astar-a) ≤ δ := by
  have hs (i : Fin T) : head q (v (join q a (x i))) * (astar-a) +
      ⟪tail q (v (join q a (x i))), ystar-x i⟫ ≤
        f (join q astar ystar)-f (join q a (x i)) := by
    have h := hsupport (join q a (x i)) (join q astar ystar)
    rwa [join_sub, inner_join] at h
  have hc := SoftCutCertificate.profile_support (fun a y => f (join q a y)) w
    (fun i => head q (v (join q a (x i))))
    (fun i => tail q (v (join q a (x i)))) x a astar δ ystar hw hwsum hs hcertificate
  have hj := hconvex.map_sum_le (t := Finset.univ) (w := w)
    (p := fun i => join q a (x i)) (fun i _ => hw i) hwsum (fun _ _ => Set.mem_univ _)
  rw [← join_weighted_sum q w hwsum a x] at hj
  change f (join q a (∑ i, w i • x i)) ≤ ∑ i, w i * f (join q a (x i)) at hj
  linarith

lemma weighted_head_bound (q : Params) {T : ℕ}
    (w : Fin T → ℝ) (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (v : Fin T → Space q) (hvn : ∀ i, ‖v i‖ ≤ q.G) :
    |∑ i, w i * head q (v i)| ≤ q.G := by
  calc
    |∑ i, w i * head q (v i)| ≤ ∑ i, |w i * head q (v i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, w i * q.G := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hw i)]
      exact mul_le_mul_of_nonneg_left ((abs_head_le q (v i)).trans (hvn i)) (hw i)
    _ = q.G := by rw [← Finset.sum_mul, hwsum, one_mul]

end LongTails.Proofs.SpikedSoftCutPrimal
