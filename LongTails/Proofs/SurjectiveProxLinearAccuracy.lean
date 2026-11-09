import LongTails.Proofs.SurjectiveProxLinearResiduals
import LongTails.Proofs.SurjectiveProxLinearStability
import LongTails.Proofs.SurjectiveProxLinearCertificateTuning

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SurjectiveProxLinearAccuracy

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearModel
open LongTails.Proofs.SurjectiveProxLinearExactModel
open LongTails.Proofs.SurjectiveProxLinearCertificate
open LongTails.Proofs.SurjectiveProxLinearResiduals
open LongTails.Proofs.SurjectiveProxLinearStability
open LongTails.Proofs.SurjectiveProxLinearTuning

lemma accurate_of_small_errors (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) (v : Primitive p)
    (hstep : ‖exactModelStep p I x‖ ≤ radius p / 4)
    (herror : ‖v.1 - gradient I.f x‖ ^ 2 + ‖v.2.1 - I.c x‖ ^ 2 +
      ‖v.2.2 - I.J x‖ ^ 2 ≤ certificateError p ^ 2)
    (hnoise : sensitivity p * (certificateError p ^ 2 + ridge p ^ 2) ≤ radius p ^ 2 / 16)
    (hrank : p.H * certificateError p ≤ 1 / 2)
    (hunit : radius p / (2 * eta p) ≤ 1)
    (hstat : radius p / (2 * eta p) + certificateError p * (1 + rho p / 2) ≤ p.ε)
    (hfeas : certificateError p + p.H * (radius p / 2) + ridge p * (rho p / 2) ≤ p.ε)
    (hcomp : ridge p * (rho p / 2) ^ 2 + (rho p / 2) *
      (certificateError p + p.H * (radius p / 2)) ≤ p.ε) :
    accurate p I (x, dualPoint p v) := by
  have hpos := valid_tuning_positive p hp
  have hsc := variance_scales_positive p hp
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.2.1
  have hg : ‖v.1 - gradient I.f x‖ ≤ certificateError p := by
    nlinarith [sq_nonneg ‖v.2.1 - I.c x‖, sq_nonneg ‖v.2.2 - I.J x‖,
      norm_nonneg (v.1 - gradient I.f x), hsc.2.2.1]
  have hc : ‖v.2.1 - I.c x‖ ≤ certificateError p := by
    nlinarith [sq_nonneg ‖v.1 - gradient I.f x‖, sq_nonneg ‖v.2.2 - I.J x‖,
      norm_nonneg (v.2.1 - I.c x), hsc.2.2.1]
  have hJ : ‖v.2.2 - I.J x‖ ≤ certificateError p := by
    nlinarith [sq_nonneg ‖v.1 - gradient I.f x‖, sq_nonneg ‖v.2.1 - I.c x‖,
      norm_nonneg (v.2.2 - I.J x), hsc.2.2.1]
  have hd0 := model_step_error_squared p I hp H x v
  have hd1 := mul_le_mul_of_nonneg_left (add_le_add_right herror (ridge p ^ 2)) hsc.1.le
  have hd : ‖exactModelStep p I x - modelStep p v‖ ≤ radius p / 4 := by
    nlinarith [hsc.2.1, norm_nonneg (exactModelStep p I x - modelStep p v)]
  have hs : ‖modelStep p v‖ ≤ radius p / 2 := by
    have h := norm_sub_le (exactModelStep p I x) (exactModelStep p I x - modelStep p v)
    rw [sub_sub_cancel] at h
    linarith
  have hsη : ‖modelStep p v‖ / eta p ≤ radius p / (2 * eta p) := by
    have h := div_le_div_of_nonneg_right hs hpos.2.2.1.le
    convert h using 1
    ring
  have hdual := multiplier_norm_from_step p I hp H x v hJ hrank
  have hdual' : ‖dualPoint p v‖ ≤ rho p / 2 := by
    have hmul := mul_le_mul_of_nonneg_left (hsη.trans hunit) (show 0 ≤ 2 * p.H by positivity)
    unfold rho
    nlinarith
  have hinside := multiplier_inside_of_norm p v hpos.1 hdual'
  obtain ⟨hf, hcp⟩ := sampled_residual_bounds p I hp x v hinside
  have hst := stationarity_residual_bound p I hp H x v
  have hmJ := mul_le_mul hJ hdual' (norm_nonneg _) hsc.2.2.1.le
  have hmH := mul_le_mul_of_nonneg_left hs hH
  have hmτ := mul_le_mul_of_nonneg_left hdual' hpos.2.2.2.le
  have hdSq : ‖dualPoint p v‖ ^ 2 ≤ (rho p / 2) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (div_nonneg hpos.1.le (by norm_num))).mpr hdual'
  have hτSq := mul_le_mul_of_nonneg_left hdSq hpos.2.2.2.le
  have hprod := mul_le_mul hdual' (add_le_add hc hmH)
    (show 0 ≤ ‖v.2.1 - I.c x‖ + p.H * ‖modelStep p v‖ by positivity)
    (show 0 ≤ rho p / 2 from div_nonneg hpos.1.le (by norm_num))
  refine ⟨(fun i => ((dualPoint_spec p v hpos.1.le).1 i).1), ?_, ?_, ?_⟩
  · change ‖gradient I.f x + transposeAction p (I.J x) (dualPoint p v)‖ ≤ p.ε
    nlinarith only [hst, hsη, hg, hmJ, hstat]
  · change ‖positivePart p (I.c x)‖ ≤ p.ε
    linarith only [hf, hc, hmH, hmτ, hfeas]
  · change (∑ i, |dualPoint p v i * I.c x i|) ≤ p.ε
    linarith only [hcp, hτSq, hprod, hcomp]


lemma certificate_accurate (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) (v : Primitive p)
    (hstep : ‖exactModelStep p I x‖ ≤ radius p / 4)
    (herror : ‖v.1 - gradient I.f x‖ ^ 2 + ‖v.2.1 - I.c x‖ ^ 2 +
      ‖v.2.2 - I.J x‖ ^ 2 ≤ certificateError p ^ 2) :
    accurate p I (x, dualPoint p v) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := SurjectiveProxLinearCertificateTuning.certificate_conditions p hp
  exact accurate_of_small_errors p I hp H x v hstep herror
    (SurjectiveProxLinearCertificateTuning.certificate_noise_scale p hp) h1 h2 h3 h4 h5

end LongTails.Proofs.SurjectiveProxLinearAccuracy
