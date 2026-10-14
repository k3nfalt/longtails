import LongTails.Proofs.NearZeroSumModel
import LongTails.Proofs.NearZeroSumOuter

open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace OracleTemplate.NearZeroSum

open LongTails.Setups.NearZeroSumGames

abbrev regularizedPublic (p : Public) (β : ℝ) : Public :=
  { p with μ := p.μ + β, ν := p.ν + β, L := p.L + β }

noncomputable def regularizedProblem {p : Public} (I : Problem p) (β : ℝ) (center : Space p) :
    Problem (regularizedPublic p β) :=
  { h := fun u => I.h u + β / 2 * ‖u.fst - center.fst‖ ^ 2 - β / 2 * ‖u.snd - center.snd‖ ^ 2
    g := I.g }

noncomputable def regularizedH {p : Public} (H : Space p → Space p) (β : ℝ) (center : Space p)
    (u : Space p) : Space p :=
  H u + WithLp.toLp 2 (β • (u.fst - center.fst), -β • (u.snd - center.snd))

lemma regularized_own_gradient {p : Public} (H G : Space p → Space p) (β : ℝ)
    (center u : Space p) :
    ownGradient (p := regularizedPublic p β) (regularizedH H β center) G u =
      ownGradient H G u + β • (u - center) := by
  apply WithLp.ofLp_injective 2
  change ((H u).fst + β • (u.fst - center.fst) + (G u).fst,
      -((H u).snd + (-β) • (u.snd - center.snd)) + (G u).snd) =
    ((H u).fst + (G u).fst + β • (u.fst - center.fst),
      -(H u).snd + (G u).snd + β • (u.snd - center.snd))
  ext <;> module

lemma joint_quadratic_x_gradient {p : Public} (β : ℝ) (center u : Space p) :
    HasGradientWithinAt (fun v : Space p => β / 2 * ‖v.fst - center.fst‖ ^ 2)
      (WithLp.toLp 2 (β • (u.fst - center.fst), (0 : p.F))) (domain p) u := by
  let T : Space p →L[ℝ] p.E := (ContinuousLinearMap.fst ℝ p.E p.F).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ p.E p.F).toContinuousLinearMap
  have h := gradient_comp_affine_within T
    (f := fun x => β / 2 * ‖x - center.fst‖ ^ 2) (b := 0) (S := domain p) (C := Set.univ)
    (x := u) (q := WithLp.toLp 2 (β • (u.fst - center.fst), (0 : p.F)))
    (by simpa [T] using
      gradient_translated_quadratic β center.fst u.fst Set.univ)
    (fun _ _ => Set.mem_univ _)
    (by intro v; simp [T, WithLp.prod_inner_apply])
  simpa [T] using h

lemma joint_quadratic_y_gradient {p : Public} (β : ℝ) (center u : Space p) :
    HasGradientWithinAt (fun v : Space p => β / 2 * ‖v.snd - center.snd‖ ^ 2)
      (WithLp.toLp 2 ((0 : p.E), β • (u.snd - center.snd))) (domain p) u := by
  let T : Space p →L[ℝ] p.F := (ContinuousLinearMap.snd ℝ p.E p.F).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ p.E p.F).toContinuousLinearMap
  have h := gradient_comp_affine_within T
    (f := fun y => β / 2 * ‖y - center.snd‖ ^ 2) (b := 0) (S := domain p) (C := Set.univ)
    (x := u) (q := WithLp.toLp 2 ((0 : p.E), β • (u.snd - center.snd)))
    (by simpa [T] using
      gradient_translated_quadratic β center.snd u.snd Set.univ)
    (fun _ _ => Set.mem_univ _)
    (by intro v; simp [T, WithLp.prod_inner_apply])
  simpa [T] using h

lemma regularized_geometry {p : Public} {I : Problem p} {H G : Space p → Space p}
    (geom : GameGeometry p I H G) (β : ℝ) (center : Space p) :
    GameGeometry (regularizedPublic p β) (regularizedProblem I β center) (regularizedH H β center) G := by
  refine ⟨geom.convexX, geom.convexY, ?_, ?_, geom.convexG, ?_, geom.gradientG, geom.lipschitzG⟩
  · intro y hy
    have h := strong_convex_add_quadratic (geom.strongX y hy) (β := β) center.fst
      (k := -β / 2 * ‖y - center.snd‖ ^ 2)
    convert h using 1
    funext x
    dsimp [regularizedProblem]
    ring
  · intro x hx
    have h := strong_convex_add_quadratic (geom.strongY x hx) (β := β) center.snd
      (k := -β / 2 * ‖x - center.fst‖ ^ 2)
    convert h using 1
    funext y
    dsimp [regularizedProblem]
    ring
  · intro u hu
    have h := gradient_add_within
      (gradient_add_within (geom.gradientH u hu) (joint_quadratic_x_gradient β center u))
      (gradient_neg_within (joint_quadratic_y_gradient β center u))
    convert h using 1
    · funext v
      dsimp [regularizedProblem]
      ring
    · apply WithLp.ofLp_injective 2
      change ((H u).fst + β • (u.fst - center.fst),
          (H u).snd + (-β) • (u.snd - center.snd)) =
        ((H u).fst + β • (u.fst - center.fst) + -0,
          (H u).snd + 0 + -(β • (u.snd - center.snd)))
      ext <;> module
    · rfl

end OracleTemplate.NearZeroSum
