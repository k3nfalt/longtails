import LongTails.Algorithms.MonotoneHessianReuse
import LongTails.Proofs.MonotoneCurvatureTuning

namespace LongTails.Proofs.MonotoneHessianParameters

open LongTails.Setups.HessianLipschitzSecondOrder
open LongTails.Algorithms.MonotoneHessianReuse

lemma gamma_pos (p : Params) (hp : spec.valid p) : 0 < gamma p :=
  Real.sqrt_pos.mpr (mul_pos hp.1 hp.2.2.1)

lemma gamma_sq (p : Params) (hp : spec.valid p) : gamma p ^ 2 = p.H * p.ε :=
  Real.sq_sqrt (mul_nonneg hp.1.le hp.2.2.1.le)

lemma scale_ge_one (p : Params) : 1 ≤ scale p := le_max_left _ _

lemma scale_pos (p : Params) : 0 < scale p := lt_of_lt_of_le zero_lt_one (scale_ge_one p)

lemma delta_pos (p : Params) (hp : spec.valid p) : 0 < delta p :=
  mul_pos (sq_pos_of_pos (scale_pos p)) (gamma_pos p hp)

lemma gamma_le_delta (p : Params) (hp : spec.valid p) : gamma p ≤ delta p := by
  have ht := scale_ge_one p
  have hγ := gamma_pos p hp
  have hsq : 1 ≤ scale p ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hsq hγ.le
  simpa only [one_mul, delta] using hh

lemma progress_pos (p : Params) (hp : spec.valid p) : 0 < progress p := by
  unfold progress
  have hγ := gamma_pos p hp
  have hH := hp.1
  positivity

lemma horizon_exhausts (p : Params) (hp : spec.valid p) : p.Δ < (stages p : ℝ) * progress p := by
  have hq := progress_pos p hp
  have hn : p.Δ / progress p < (stages p : ℝ) := by
    have hh := Nat.le_ceil (p.Δ / progress p)
    simp only [stages, Nat.cast_add, Nat.cast_one]
    linarith
  exact (div_lt_iff₀ hq).mp hn

lemma distance_scale_identities (p : Params) (hp : spec.valid p) :
    p.H * MonotoneCurvatureTuning.distanceScale p.H (gamma p) = gamma p / 2 ^ 30 ∧
    gamma p * MonotoneCurvatureTuning.distanceScale p.H (gamma p) = p.ε / 2 ^ 30 := by
  have hH := hp.1.ne'
  have hs := gamma_sq p hp
  constructor
  · unfold MonotoneCurvatureTuning.distanceScale
    field_simp
  · unfold MonotoneCurvatureTuning.distanceScale
    field_simp
    nlinarith only [hs]

lemma relative_tolerance (p : Params) (hp : spec.valid p) :
    relativeTolerance p = 1 / (64 * scale p ^ 2) := by
  have hγ := (gamma_pos p hp).ne'
  unfold relativeTolerance delta
  field_simp

lemma relative_tolerance_range (p : Params) (hp : spec.valid p) :
    0 < relativeTolerance p ∧ relativeTolerance p ≤ 1 := by
  rw [relative_tolerance p hp]
  have ht := scale_ge_one p
  have ht0 := scale_pos p
  constructor
  · positivity
  · apply (div_le_one (by positivity)).mpr
    nlinarith

lemma degree_sufficient (p : Params) :
    2 * Real.log (16 * max 1 (Module.finrank ℝ p.E : ℝ) / relativeTolerance p) /
      Real.sqrt (relativeTolerance p) ≤ degree p := Nat.le_ceil _

lemma repetitions_sufficient (p : Params) :
    16 * Real.log ((stages p : ℝ) / p.ρ) ≤ repetitions p := Nat.le_ceil _

end LongTails.Proofs.MonotoneHessianParameters
