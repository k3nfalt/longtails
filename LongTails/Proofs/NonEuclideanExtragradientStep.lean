import LongTails.Algorithms.NonEuclideanExtragradient
import LongTails.Proofs.NonEuclideanWeakMintyGeometry

namespace LongTails.Proofs.NonEuclideanExtragradientStep

open LongTails.Setups.NonEuclideanWeakMinty
open LongTails.Algorithms.NonEuclideanExtragradient
open LongTails.Proofs.NonEuclideanWeakMintyGeometry

lemma direction_spec (d : Public) (g : d.E →L[ℝ] ℝ) :
    ‖LongTails.Algorithms.PowerDualAveraging.direction g‖ ≤ ‖g‖ ∧
      g (LongTails.Algorithms.PowerDualAveraging.direction g) = ‖g‖ ^ 2 := by
  classical
  have h := PowerMirrorGeometry.exists_direction g
  simp only [LongTails.Algorithms.PowerDualAveraging.direction, dite_eq_left h]
  exact Classical.choose_spec h

lemma mirror_spec (d : Public) (hd : d.Valid) (x : d.E) (g : d.E →L[ℝ] ℝ) :
    ∀ w, (d.μ / (10 * d.L)) * g (mirror d x g) + d.bregman (mirror d x g) x ≤
      (d.μ / (10 * d.L)) * g w + d.bregman w x := by
  classical
  have hex : ∃ z, ∀ w, (d.μ / (10 * d.L)) * g z + d.bregman z x ≤
      (d.μ / (10 * d.L)) * g w + d.bregman w x := by
    obtain ⟨z, hz⟩ := exists_mirror_step hd.2.2.2.1 hd.2.2.2.2.1
      hd.2.2.2.2.2 x g (γ := d.μ / (10 * d.L))
    refine ⟨z, fun w => ?_⟩
    simpa only [Public.bregman, add_sub_assoc] using hz w
  simpa only [mirror, dite_eq_left hex] using Classical.choose_spec hex

lemma step_descent (d : Public) (hd : d.Valid) (F : d.E → d.E →L[ℝ] ℝ)
    (hlip : ∀ x y, ‖F x - F y‖ ≤ d.L * ‖x - y‖)
    (u : d.E) (hminty : ∀ x, -d.ρ * ‖F x‖ ^ 2 ≤ F x (x - u)) (x : d.E) :
    d.bregman u (mirror d x (F (predictor d x (F x)))) ≤
      d.bregman u x - d.μ / (400 * d.L ^ 2) * ‖F x‖ ^ 2 := by
  have hv := direction_spec d (F x)
  have hp := predictor_alignment hd.1 hd.2.1 hd.2.2.1 hlip hminty hv.1 hv.2
  change ‖F (predictor d x (F x))‖ ≤ 3 / 2 * ‖F x‖ ∧ _ at hp
  have hm := mirror_step_bound hd.2.2.2.1
    (show 0 ≤ d.μ / (10 * d.L) from div_nonneg hd.2.2.2.1.le (mul_nonneg (by norm_num) hd.1.le))
    hd.2.2.2.2.1 hd.2.2.2.2.2
    (x := x) (u := u) (g := F (predictor d x (F x)))
    (z := mirror d x (F (predictor d x (F x))))
    (fun w => by
      simpa only [Public.bregman, add_sub_assoc] using
        mirror_spec d hd x (F (predictor d x (F x))) w)
  exact descent_algebra hd.1 hd.2.2.2.1 (norm_nonneg _) (norm_nonneg _)
    hp.1 hp.2 hm

end LongTails.Proofs.NonEuclideanExtragradientStep
