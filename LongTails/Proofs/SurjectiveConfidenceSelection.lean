import LongTails.Proofs.SurjectiveProxLinearAccuracy

namespace LongTails.Proofs.SurjectiveConfidenceSelection

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearExactModel
open LongTails.Proofs.SurjectiveProxLinearTuning

lemma robust_step_error (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) (v : Primitive p)
    (he : ‖v.1 - gradient I.f x‖ ^ 2 + ‖v.2.1 - I.c x‖ ^ 2 +
      ‖v.2.2 - I.J x‖ ^ 2 ≤ (certificateError p / 4) ^ 2) :
    ‖exactModelStep p I x - modelStep p v‖ ≤ radius p / 16 := by
  have hm : (p.m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hp.1).ne'
  have hH : p.H ≠ 0 := (lt_of_lt_of_le zero_lt_one hp.2.1).ne'
  have hid : sensitivity p * ((certificateError p / 4) ^ 2 + ridge p ^ 2) =
      (65 / 65536 : ℝ) * radius p ^ 2 := by
    unfold sensitivity certificateError ridge radius
    field_simp [hm, hH]
    ring
  have hpos := variance_scales_positive p hp
  have h1 := SurjectiveProxLinearStability.model_step_error_squared p I hp H x v
  have h2 := mul_le_mul_of_nonneg_left (add_le_add_right he (ridge p ^ 2)) hpos.1.le
  rw [add_comm (ridge p ^ 2) ((certificateError p / 4) ^ 2), hid] at h2
  nlinarith [norm_nonneg (exactModelStep p I x - modelStep p v), hpos.2.1]

lemma selected_accurate (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) {ι : Type*} (x : ι → p.E) (v : ι → Primitive p)
    (chosen good : ι)
    (he : ∀ i, ‖(v i).1 - gradient I.f (x i)‖ ^ 2 +
      ‖(v i).2.1 - I.c (x i)‖ ^ 2 + ‖(v i).2.2 - I.J (x i)‖ ^ 2 ≤
        (certificateError p / 4) ^ 2)
    (hgood : ‖exactModelStep p I (x good)‖ ≤ radius p / 8)
    (hmin : ‖modelStep p (v chosen)‖ ≤ ‖modelStep p (v good)‖) :
    accurate p I (x chosen, dualPoint p (v chosen)) := by
  have hg := robust_step_error p I hp H (x good) (v good) (he good)
  have hc := robust_step_error p I hp H (x chosen) (v chosen) (he chosen)
  have hng := norm_sub_le (exactModelStep p I (x good))
    (exactModelStep p I (x good) - modelStep p (v good))
  rw [sub_sub_cancel] at hng
  have hnc := norm_add_le (exactModelStep p I (x chosen) - modelStep p (v chosen))
    (modelStep p (v chosen))
  rw [sub_add_cancel] at hnc
  apply SurjectiveProxLinearAccuracy.certificate_accurate p I hp H
  · linarith
  · have h := he chosen
    nlinarith [sq_nonneg (certificateError p)]

end LongTails.Proofs.SurjectiveConfidenceSelection
