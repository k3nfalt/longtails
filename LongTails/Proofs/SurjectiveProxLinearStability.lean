import LongTails.Proofs.SurjectiveProxLinearExactModel
import LongTails.Proofs.SurjectiveProxLinearTuning

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SurjectiveProxLinearStability

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.ProxLinearDualSensitivity
open LongTails.Proofs.SurjectiveProxLinearModel
open LongTails.Proofs.SurjectiveProxLinearExactModel

lemma model_step_error (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) (v : Primitive p) :
    ‖exactModelStep p I x - modelStep p v‖ ≤
      eta p * (1 + p.H ^ 4) * ‖v.1 - gradient I.f x‖ +
      eta p * (rho p * p.m + p.H ^ 3 * (p.H + 2 * p.H * (rho p * p.m))) *
        ‖v.2.2 - I.J x‖ +
      p.H ^ 3 * ‖v.2.1 - I.c x‖ + p.H ^ 3 * (rho p * p.m) * ridge p := by
  have hρ := (valid_tuning_positive p hp).1.le
  have hη := (valid_tuning_positive p hp).2.2.1.le
  have hτ := (valid_tuning_positive p hp).2.2.2.le
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.2.1
  have hT : ‖transposeContinuous p (I.J x)‖ ≤ p.H :=
    (norm_transposeContinuous_le p (I.J x)).trans (H.jacobianBound x)
  have hS : ‖transposeContinuous p (OracleTemplate.clip p.H v.2.2)‖ ≤ p.H :=
    (norm_transposeContinuous_le p _).trans (OracleTemplate.norm_clip_le hH _)
  have h := fullrank_primal_step_error
    (transposeContinuous p (I.J x)) (transposeContinuous p (OracleTemplate.clip p.H v.2.2))
    (gradient I.f x) (OracleTemplate.clip p.H v.1) (I.c x) v.2.1
    (exactDualPoint p I x) (dualPoint p v) hη hτ hH hH hT hS
    (OracleTemplate.norm_clip_le hH v.1)
    (norm_mem_dualBox_le p hp.1 hρ (dualPoint_spec p v hρ).1)
    (H.surjective x)
    (exactDualPoint_vi p I x hρ (dualPoint_spec p v hρ).1)
    (dualPoint_vi p v hρ (exactDualPoint_spec p I x hρ).1)
  have hg : ‖gradient I.f x - OracleTemplate.clip p.H v.1‖ ≤ ‖v.1 - gradient I.f x‖ := by
    rw [norm_sub_rev]
    exact OracleTemplate.norm_clip_sub_le hH (H.gradientBound x) v.1
  have hJ : ‖transposeContinuous p (I.J x) -
      transposeContinuous p (OracleTemplate.clip p.H v.2.2)‖ ≤ ‖v.2.2 - I.J x‖ := by
    apply (norm_transposeContinuous_sub_le p _ _).trans
    rw [norm_sub_rev]
    exact OracleTemplate.norm_clip_sub_le hH (H.jacobianBound x) v.2.2
  have hg' := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ eta p * (1 + p.H ^ 2 * p.H ^ 2) by positivity)
  have hJ' := mul_le_mul_of_nonneg_left hJ
    (show 0 ≤ eta p * (rho p * p.m + p.H * p.H ^ 2 *
      (p.H + 2 * p.H * (rho p * p.m))) by positivity)
  simp only [transposeContinuous_apply] at h
  unfold exactModelStep modelStep
  rw [norm_sub_rev (I.c x) v.2.1] at h
  nlinarith

lemma model_step_error_squared (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) (v : Primitive p) :
    ‖exactModelStep p I x - modelStep p v‖ ^ 2 ≤ sensitivity p *
      (‖v.1 - gradient I.f x‖ ^ 2 + ‖v.2.1 - I.c x‖ ^ 2 +
        ‖v.2.2 - I.J x‖ ^ 2 + ridge p ^ 2) := by
  have ht := (valid_tuning_positive p hp).2.2.2.le
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.2.1
  obtain ⟨ha, hb, hc, hd⟩ :=
    SurjectiveProxLinearTuning.parameter_sensitivity_coefficients p hp
  have ha' := mul_le_mul_of_nonneg_right ha (norm_nonneg (v.1 - gradient I.f x))
  have hb' := mul_le_mul_of_nonneg_right hb (norm_nonneg (v.2.2 - I.J x))
  have hc' := mul_le_mul_of_nonneg_right hc (norm_nonneg (v.2.1 - I.c x))
  have hd' := mul_le_mul_of_nonneg_right hd ht
  have he := model_step_error p I hp H x v
  have hn : ‖exactModelStep p I x - modelStep p v‖ ≤
      (16 * p.m * p.H ^ 6) *
        (‖v.1 - gradient I.f x‖ + ‖v.2.2 - I.J x‖ + ‖v.2.1 - I.c x‖ + ridge p) := by
    nlinarith
  have hs := SurjectiveProxLinearTuning.four_term_square
    (a := ‖v.1 - gradient I.f x‖) (b := ‖v.2.2 - I.J x‖)
    (c := ‖v.2.1 - I.c x‖) (d := ridge p)
  calc
    _ ≤ ((16 * p.m * p.H ^ 6) *
        (‖v.1 - gradient I.f x‖ + ‖v.2.2 - I.J x‖ + ‖v.2.1 - I.c x‖ + ridge p)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
    _ = (16 * p.m * p.H ^ 6) ^ 2 *
        (‖v.1 - gradient I.f x‖ + ‖v.2.2 - I.J x‖ + ‖v.2.1 - I.c x‖ + ridge p) ^ 2 := by ring
    _ ≤ (16 * p.m * p.H ^ 6) ^ 2 *
        (4 * (‖v.1 - gradient I.f x‖ ^ 2 + ‖v.2.2 - I.J x‖ ^ 2 +
          ‖v.2.1 - I.c x‖ ^ 2 + ridge p ^ 2)) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by unfold sensitivity; ring

end LongTails.Proofs.SurjectiveProxLinearStability
