import LongTails.Proofs.StochasticEqualityExecution
import LongTails.Proofs.StochasticEqualityEnergy

namespace LongTails.Proofs.StochasticEqualityValidation

open OracleTemplate
open LongTails.Setups.StochasticRegularEqualities
open LongTails.Algorithms.MatrixPolar
open LongTails.Algorithms.StochasticEquality
open LongTails.Algorithms.StochasticEqualityDirection
open LongTails.Proofs.StochasticEqualityGeometry
open LongTails.Proofs.StochasticEqualityExecution

lemma clipped_operator_error (p : Public) {t : ℝ} (hL : 0 ≤ p.Lc)
    (u v : Reply p) (hu : ‖u.2.2‖ ≤ p.Lc) (hv : ‖v.2.2 - u.2.2‖ ≤ t) :
    ‖operatorEquiv p.d p.m u.2.2 - operatorEquiv p.d p.m (clip p.Lc v.2.2)‖ ≤ t := by
  rw [norm_sub_rev, ← map_sub]
  exact (MomentumSeparationInstance.spectralNorm_le_norm _).trans
    ((norm_clip_sub_le hL hu _).trans hv)

lemma validate_score (p : Public) (cfg : Config) (x : Point p.d) (v : Reply p)
    (y : Point p.d × Point p.m) (hy : validate p cfg x v = some y) :
    let J := operatorEquiv p.d p.m (clip p.Lc v.2.2)
    regular (p.ν / 2) J ∧ ‖v.1 + J y.2‖ ^ 2 + ‖v.2.1‖ ^ 2 ≤ p.ε ^ 2 / 16 := by
  classical
  unfold validate at hy
  dsimp only at hy
  split_ifs at hy with h
  cases Option.some.inj hy
  exact h

lemma validate_sound (p : Public) (cfg : Config) {t : ℝ}
    (hν : 0 < p.ν) (hL : 0 ≤ p.Lc) (hG : 0 ≤ cfg.gradientCap) (hε : 0 ≤ p.ε)
    (u v : Reply p) (hu : ‖u.2.2‖ ≤ p.Lc)
    (hg : ‖v.1 - u.1‖ ≤ t) (hc : ‖v.2.1 - u.2.1‖ ≤ t) (hJ : ‖v.2.2 - u.2.2‖ ≤ t)
    (x : Point p.d) (y : Point p.d × Point p.m) (hy : validate p cfg x v = some y) :
    ‖u.1 + operatorEquiv p.d p.m u.2.2 y.2‖ ≤ p.ε / 4 + (1 + 2 * cfg.gradientCap / p.ν) * t ∧
      ‖u.2.1‖ ≤ p.ε / 4 + t := by
  let A := operatorEquiv p.d p.m u.2.2
  let B := operatorEquiv p.d p.m (clip p.Lc v.2.2)
  have ht : 0 ≤ t := (norm_nonneg _).trans hg
  have hs := (validate_score p cfg x v y hy).2
  have hμ := (validate_properties p cfg hν hG x v y hy).2
  have hAB : ‖A - B‖ ≤ t := clipped_operator_error p hL u v hu hJ
  have heg : ‖v.1 + B y.2‖ ≤ p.ε / 4 := by
    dsimp only [B]
    nlinarith [sq_nonneg ‖v.2.1‖, norm_nonneg (v.1 + B y.2)]
  have hec : ‖v.2.1‖ ≤ p.ε / 4 := by
    nlinarith [sq_nonneg ‖v.1 + B y.2‖, norm_nonneg v.2.1]
  constructor
  · have he : u.1 + A y.2 = (v.1 + B y.2) + (u.1 - v.1) + (A - B) y.2 := by
      simp only [sub_apply]
      abel
    change ‖u.1 + A y.2‖ ≤ _
    rw [he]
    calc
      _ ≤ ‖v.1 + B y.2‖ + ‖u.1 - v.1‖ + ‖(A - B) y.2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ p.ε / 4 + t + t * (2 * cfg.gradientCap / p.ν) := by
        apply add_le_add
        · exact add_le_add heg (by simpa only [norm_sub_rev] using hg)
        · exact ((A - B).le_opNorm _).trans (mul_le_mul hAB hμ (norm_nonneg _) ht)
      _ = _ := by ring
  · have hh := norm_sub_norm_le u.2.1 v.2.1
    have hh' : ‖u.2.1 - v.2.1‖ ≤ t := by simpa only [norm_sub_rev] using hc
    linarith only [hh, hh', hec]

lemma validation_error_scale {S ε : ℝ} (hS : 1 ≤ S) (hε : 0 ≤ ε) :
    (1 + 8000 * S ^ 7) * (ε / (10 ^ 6 * S ^ 7)) ≤ ε / 12 := by
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hp : 1 ≤ S ^ 7 := one_le_pow₀ hS
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < (10 : ℝ) ^ 6 * S ^ 7)).mpr
  nlinarith [mul_nonneg hε (sub_nonneg.mpr hp)]

lemma tuned_validation_error (p : Params) (hp : spec.valid p) :
    let cfg := tuning p.toPublic
    (1 + 2 * cfg.gradientCap / p.ν) * cfg.validationTolerance ≤ p.ε / 12 ∧
      cfg.validationTolerance ≤ p.ε / 12 := by
  let S := StochasticEqualityTuning.scale p.toPublic
  let cfg := tuning p.toPublic
  obtain ⟨hS, _, _, _, _, _, hinv, _, _⟩ := StochasticEqualityTuning.scale_bounds p hp
  have hS1 : 1 ≤ S := by dsimp [S]; linarith only [hS]
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS1
  have hν := hp.2.2.2.1
  have hε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hmu : 2 * cfg.gradientCap / p.ν ≤ 8000 * S ^ 7 := by
    change 2 * (4000 * S ^ 6) / p.ν ≤ 8000 * S ^ 7
    have hh := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 8000 * S ^ 6 by positivity)
    calc
      2 * (4000 * S ^ 6) / p.ν = 8000 * S ^ 6 * (1 / p.ν) := by ring
      _ ≤ 8000 * S ^ 6 * S := hh
      _ = 8000 * S ^ 7 := by ring
  have ht : 0 ≤ cfg.validationTolerance := by
    change 0 ≤ p.ε / (10 ^ 6 * S ^ 7)
    positivity
  have hsmall := validation_error_scale hS1 hε.le
  have hc : (1 + 2 * cfg.gradientCap / p.ν) * cfg.validationTolerance ≤ p.ε / 12 := by
    exact (mul_le_mul_of_nonneg_right (add_le_add le_rfl hmu) ht).trans hsmall
  refine ⟨hc, ?_⟩
  have hμ0 : 0 ≤ 2 * cfg.gradientCap / p.ν := by
    change 0 ≤ 2 * (4000 * S ^ 6) / p.ν
    positivity
  nlinarith only [hc, mul_nonneg hμ0 ht]

lemma admissible_validate_sound (p : Params) (hp : spec.valid p)
    (I : Instance p.toPublic) (O : Oracle (Point p.d) (Reply p.toPublic))
    (hI : spec.admissible p I O) (x : Point p.d) (v : Reply p.toPublic)
    (hg : ‖v.1 - gradient I.f x‖ ≤ (tuning p.toPublic).validationTolerance)
    (hc : ‖v.2.1 - I.c x‖ ≤ (tuning p.toPublic).validationTolerance)
    (hJ : ‖v.2.2 - jacobian I x‖ ≤ (tuning p.toPublic).validationTolerance)
    (y : Point p.d × Point p.m) (hy : validate p.toPublic (tuning p.toPublic) x v = some y) :
    ‖gradient I.f y.1 + (fderiv ℝ I.c y.1).adjoint y.2‖ ^ 2 + ‖I.c y.1‖ ^ 2 ≤ p.ε ^ 2 / 4 := by
  obtain ⟨_, hG, _, _⟩ := StochasticEqualityTuning.tuning_geometry p hp
  have hν := hp.2.2.2.1
  have hε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hcg, hcc⟩ := tuned_validation_error p hp
  have hs := validate_sound p.toPublic (tuning p.toPublic) hν hp.2.2.2.2.2.1 hG hε.le
    (StochasticEqualityModel.truth I x) v (hI.2.2.2.2.2.1 x) hg hc hJ x y hy
  have hyx := (validate_properties p.toPublic (tuning p.toPublic) hν hG x v y hy).1
  rw [hyx]
  rw [StochasticEqualityModel.truth_operator] at hs
  have hstation : ‖gradient I.f x + (fderiv ℝ I.c x).adjoint y.2‖ ≤ p.ε / 3 := by
    have hh := hs.1
    change ‖gradient I.f x + (fderiv ℝ I.c x).adjoint y.2‖ ≤ _ at hh
    linarith only [hh, hcg]
  have hfeas : ‖I.c x‖ ≤ p.ε / 3 := by
    have hh := hs.2
    change ‖I.c x‖ ≤ _ at hh
    linarith only [hh, hcc]
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ p.ε / 3)).mpr hstation
  have hcsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ p.ε / 3)).mpr hfeas
  nlinarith only [hsquare, hcsquare, sq_nonneg p.ε]

lemma validate_complete (p : Public) (cfg : Config) {t : ℝ}
    (hν : 0 < p.ν) (hL : 0 ≤ p.Lc) (hG : 0 ≤ cfg.gradientCap) (hε : 0 ≤ p.ε)
    (u v : Reply p) (hu : ‖u.2.2‖ ≤ p.Lc) (hug : ‖u.1‖ ≤ cfg.gradientCap)
    (hreg : regular p.ν (operatorEquiv p.d p.m u.2.2))
    (hg : ‖v.1 - u.1‖ ≤ t) (hc : ‖v.2.1 - u.2.1‖ ≤ t) (hJ : ‖v.2.2 - u.2.2‖ ≤ t)
    (htν : t ≤ p.ν / 2)
    (hstation : ‖tangent (operatorEquiv p.d p.m u.2.2) u.1‖ + (3 + cfg.gradientCap / p.ν) * t ≤ p.ε / 8)
    (hfeas : ‖u.2.1‖ + t ≤ p.ε / 8) (x : Point p.d) :
    ∃ μ, validate p cfg x v = some (x, μ) := by
  classical
  let A := operatorEquiv p.d p.m u.2.2
  let B := operatorEquiv p.d p.m (clip p.Lc v.2.2)
  let w := clip cfg.gradientCap v.1
  let lam := multiplier A u.1
  let μ := thresholdedMultiplier p.ν B w
  have ht : 0 ≤ t := (norm_nonneg _).trans hg
  have hAB : ‖A - B‖ ≤ t := clipped_operator_error p hL u v hu hJ
  have hBA : ‖B - A‖ ≤ t := by simpa only [norm_sub_rev] using hAB
  have hB : regular (p.ν / 2) B := by
    by_contra hh
    have he := error_of_rejected hreg hh
    exact (not_lt_of_ge (hBA.trans htν)) he
  have hw : ‖w - u.1‖ ≤ t := (norm_clip_sub_le hG hug v.1).trans hg
  have hraw : ‖v.1 - w‖ ≤ 2 * t := by
    have hh' : ‖u.1 - w‖ ≤ t := by simpa only [norm_sub_rev] using hw
    have he : v.1 - w = (v.1 - u.1) + (u.1 - w) := by abel
    rw [he]
    exact (norm_add_le _ _).trans (by linarith only [hg, hh'])
  have hlam : ‖lam‖ ≤ cfg.gradientCap / p.ν :=
    (norm_multiplier_le hν hreg u.1).trans (div_le_div_of_nonneg_right hug hν.le)
  have hshift : ‖w + B lam‖ ≤ ‖tangent A u.1‖ + t + t * (cfg.gradientCap / p.ν) := by
    have he : w + B lam = tangent A u.1 + (w - u.1) + (B - A) lam := by
      simp only [tangent, lam, sub_apply]
      abel
    rw [he]
    calc
      _ ≤ ‖tangent A u.1‖ + ‖w - u.1‖ + ‖(B - A) lam‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖tangent A u.1‖ + t + t * (cfg.gradientCap / p.ν) :=
        add_le_add (add_le_add le_rfl hw)
          (((B - A).le_opNorm lam).trans (mul_le_mul hBA hlam (norm_nonneg _) ht))
  have hμ : μ = multiplier B w := by simp only [μ, thresholdedMultiplier, ite_eq_left hB]
  have hres : ‖v.1 + B μ‖ ≤ p.ε / 8 := by
    have hls := (norm_tangent_le_shift (half_pos hν) hB w lam).trans hshift
    have he : v.1 + B μ = (v.1 - w) + tangent B w := by
      rw [hμ]
      simp only [tangent]
      abel
    rw [he]
    apply (norm_add_le _ _).trans
    change ‖v.1 - w‖ + ‖tangent B w‖ ≤ _
    nlinarith only [hraw, hls, hstation]
  have hcv : ‖v.2.1‖ ≤ p.ε / 8 := by
    have hh := norm_sub_norm_le v.2.1 u.2.1
    linarith only [hh, hc, hfeas]
  have hs : ‖v.1 + B μ‖ ^ 2 + ‖v.2.1‖ ^ 2 ≤ p.ε ^ 2 / 16 := by
    have h1 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ p.ε / 8)).mpr hres
    have h2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ p.ε / 8)).mpr hcv
    nlinarith only [h1, h2, sq_nonneg p.ε]
  refine ⟨μ, ?_⟩
  exact ite_eq_left ⟨hB, hs⟩


lemma tuned_validation_completeness (p : Params) (hp : spec.valid p) :
    let S := StochasticEqualityTuning.scale p.toPublic
    let cfg := tuning p.toPublic
    cfg.validationTolerance ≤ p.ν / 2 ∧
      p.ε / (32 * S) + (3 + cfg.gradientCap / p.ν) * cfg.validationTolerance ≤ p.ε / 8 ∧
      p.ε / (32 * S) + cfg.validationTolerance ≤ p.ε / 8 := by
  let S := StochasticEqualityTuning.scale p.toPublic
  let cfg := tuning p.toPublic
  obtain ⟨hS, _, _, _, _, _, hinv, _, _⟩ := StochasticEqualityTuning.scale_bounds p hp
  have hS1 : 1 ≤ S := by dsimp [S]; linarith only [hS]
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS1
  have hν := hp.2.2.2.1
  have hε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hε1 := hp.2.2.2.2.2.2.2.2.2.2.2.2
  have ht : 0 ≤ cfg.validationTolerance := by
    change 0 ≤ p.ε / (10 ^ 6 * S ^ 7)
    positivity
  have hxi : p.ε / (32 * S) ≤ p.ε / 32 := by
    apply (div_le_iff₀ (by positivity : 0 < 32 * S)).mpr
    nlinarith only [mul_nonneg hε.le (sub_nonneg.mpr hS1)]
  have hmu : cfg.gradientCap / p.ν ≤ 4000 * S ^ 7 := by
    change (4000 * S ^ 6) / p.ν ≤ 4000 * S ^ 7
    calc
      _ = 4000 * S ^ 6 * (1 / p.ν) := by ring
      _ ≤ 4000 * S ^ 6 * S := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  have hp7 : 1 ≤ S ^ 7 := one_le_pow₀ hS1
  have hcoeff : 3 + cfg.gradientCap / p.ν ≤ 1 + 8000 * S ^ 7 := by
    linarith only [hmu, hp7]
  have hsmall : (3 + cfg.gradientCap / p.ν) * cfg.validationTolerance ≤ p.ε / 12 :=
    (mul_le_mul_of_nonneg_right hcoeff ht).trans (validation_error_scale hS1 hε.le)
  have htiny := (tuned_validation_error p hp).2
  change cfg.validationTolerance ≤ p.ε / 12 at htiny
  change cfg.validationTolerance ≤ p.ν / 2 ∧
    p.ε / (32 * S) + (3 + cfg.gradientCap / p.ν) * cfg.validationTolerance ≤ p.ε / 8 ∧
    p.ε / (32 * S) + cfg.validationTolerance ≤ p.ε / 8
  refine ⟨?_, by linarith only [hxi, hsmall, hε], by linarith only [hxi, htiny, hε]⟩
  have hνS : 1 ≤ p.ν * S := by
    have hh := (div_le_iff₀ hν).mp hinv
    nlinarith only [hh]
  have hp6 : 1 ≤ S ^ 6 := one_le_pow₀ hS1
  have hνS7 : 1 ≤ p.ν * S ^ 7 := by
    have hh := mul_le_mul_of_nonneg_left hp6 (show 0 ≤ p.ν * S by positivity)
    nlinarith only [hνS, hh]
  change p.ε / (10 ^ 6 * S ^ 7) ≤ p.ν / 2
  apply (div_le_iff₀ (by positivity : 0 < (10 : ℝ) ^ 6 * S ^ 7)).mpr
  nlinarith only [hε1, hνS7]

lemma admissible_validate_complete (p : Params) (hp : spec.valid p)
    (I : Instance p.toPublic) (O : Oracle (Point p.d) (Reply p.toPublic))
    (hI : spec.admissible p I O) (x : Point p.d) (v : Reply p.toPublic)
    (hcap : ‖gradient I.f x‖ ≤ (tuning p.toPublic).gradientCap)
    (hres : StochasticEqualityEnergy.residual p.toPublic (StochasticEqualityModel.truth I)
      (10 ^ 10 * (StochasticEqualityTuning.scale p.toPublic) ^ 24) x ≤
        (p.ε / (32 * StochasticEqualityTuning.scale p.toPublic)) ^ 2)
    (hg : ‖v.1 - gradient I.f x‖ ≤ (tuning p.toPublic).validationTolerance)
    (hc : ‖v.2.1 - I.c x‖ ≤ (tuning p.toPublic).validationTolerance)
    (hJ : ‖v.2.2 - jacobian I x‖ ≤ (tuning p.toPublic).validationTolerance) :
    ∃ μ, validate p.toPublic (tuning p.toPublic) x v = some (x, μ) := by
  let S := StochasticEqualityTuning.scale p.toPublic
  let cfg := tuning p.toPublic
  have hS : 0 < S := lt_of_lt_of_le (by norm_num) (StochasticEqualityTuning.scale_bounds p hp).1
  have hν := hp.2.2.2.1
  have hε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hxi : 0 ≤ p.ε / (32 * S) := by positivity
  have hk := (StochasticEqualityEnergy.admissible_residual_controls_kkt p hp I O hI x).trans hres
  have htangent : ‖tangent ((fderiv ℝ I.c x).adjoint) (gradient I.f x)‖ ≤ p.ε / (32 * S) := by
    nlinarith [sq_nonneg ‖I.c x‖, norm_nonneg (tangent ((fderiv ℝ I.c x).adjoint) (gradient I.f x))]
  have hconstraint : ‖I.c x‖ ≤ p.ε / (32 * S) := by
    nlinarith [sq_nonneg ‖tangent ((fderiv ℝ I.c x).adjoint) (gradient I.f x)‖, norm_nonneg (I.c x)]
  obtain ⟨hνt, hstat, hfeas⟩ := tuned_validation_completeness p hp
  obtain ⟨_, hG, _, _⟩ := StochasticEqualityTuning.tuning_geometry p hp
  apply validate_complete p.toPublic cfg hν hp.2.2.2.2.2.1 hG hε.le
    (StochasticEqualityModel.truth I x) v (hI.2.2.2.2.2.1 x) hcap
    (StochasticEqualityModel.admissible_truth_regular p I O hI x) hg hc hJ hνt ?_ ?_ x
  · rw [StochasticEqualityModel.truth_operator]
    exact (add_le_add htangent le_rfl).trans hstat
  · exact (add_le_add hconstraint le_rfl).trans hfeas

end LongTails.Proofs.StochasticEqualityValidation
