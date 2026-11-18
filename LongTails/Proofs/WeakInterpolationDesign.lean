import LongTails.Algorithms.WeightedInterpolationSgd
import LongTails.Proofs.InterpolationWeights

namespace LongTails.Proofs.WeakInterpolationDesign

open LongTails.Setups.DistributedWeakInterpolation LongTails.Algorithms.WeakInterpolationDesign
open LongTails.Algorithms.WeightedInterpolationSgd

variable {p : Params}

lemma threshold_spec (hp : spec.valid p) :
    0 ≤ threshold p ∧ ∑ i, profile p i = (p.n : ℝ) * p.μ := by
  classical
  obtain ⟨hh,hL,hμ,hm,_⟩ := hp
  have ex := InterpolationWeights.exists_threshold p.L (fun i => (p.h i : ℝ)) (p.n * p.μ)
    hL (fun i => by exact_mod_cast hh i) (by positivity) hm
  change ∃ c, 0 ≤ c ∧ ∑ i, curvature p.L (fun j => p.h j) c i = (p.n : ℝ) * p.μ at ex
  simpa [profile, threshold, dite_eq_left ex] using ex.choose_spec

lemma profile_nonneg (hp : spec.valid p) (i : Fin p.n) : 0 ≤ profile p i :=
  le_min (hp.2.1 i) (mul_nonneg (threshold_spec hp).1 (p.h i).coe_nonneg)

lemma weight_nonneg (hp : spec.valid p) (i : Fin p.n) : 0 ≤ weights p i :=
  div_nonneg (profile_nonneg hp i) (p.h i).coe_nonneg

lemma profile_pos_some (hp : spec.valid p) : ∃ i, 0 < profile p i := by
  by_contra! h
  have hz := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
  rw [(threshold_spec hp).2] at hz
  exact (not_lt_of_ge hz) (mul_pos (by exact_mod_cast p.n.pos) hp.2.2.1)

lemma information_pos (hp : spec.valid p) : 0 < information p := by
  obtain ⟨i,hi⟩ := profile_pos_some hp
  have hw : 0 < weights p i := div_pos hi (by exact_mod_cast hp.1 i)
  exact (mul_pos hw hi).trans_le (Finset.single_le_sum
    (fun j _ => mul_nonneg (weight_nonneg hp j) (profile_nonneg hp j)) (Finset.mem_univ i))

lemma cap_pos (hp : spec.valid p) : 0 < largestCurvature p := by
  obtain ⟨i,hi⟩ := profile_pos_some hp
  have hL : profile p i ≤ p.L i := min_le_left _ _
  exact (mul_pos hi (hi.trans_le hL)).trans_le (Finset.le_sup' (fun j => profile p j * p.L j) (Finset.mem_univ i))

lemma speed_pos (hp : spec.valid p) : 0 < ∑ i, (p.h i : ℝ)⁻¹ := by
  obtain ⟨i, _⟩ := profile_pos_some hp
  have hh : 0 < (p.h i : ℝ) := by exact_mod_cast hp.1 i
  exact (inv_pos.mpr hh).trans_le (Finset.single_le_sum
    (fun j _ => inv_nonneg.mpr (p.h j).coe_nonneg) (Finset.mem_univ i))

lemma smoothness_pos (hp : spec.valid p) : 0 < smoothness p :=
  mul_pos (mul_pos (by norm_num) (speed_pos hp)) (cap_pos hp)

lemma smooth_majorant (hp : spec.valid p) :
    ∑ i, weights p i * p.L i ≤ smoothness p := by
  calc
    _ ≤ ∑ i, (p.h i : ℝ)⁻¹ * largestCurvature p := by
      apply Finset.sum_le_sum
      intro i _
      change profile p i / (p.h i : ℝ) * p.L i ≤ _
      rw [div_mul_eq_mul_div, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun j => profile p j * p.L j) (Finset.mem_univ i))
        (inv_nonneg.mpr (p.h i).coe_nonneg)
    _ ≤ _ := by
      rw [← Finset.sum_mul, smoothness]
      linarith [mul_nonneg (speed_pos hp).le (cap_pos hp).le]

lemma information_le (hp : spec.valid p) : information p ≤ smoothness p :=
  (Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (show profile p i ≤ p.L i from min_le_left _ _) (weight_nonneg hp i))).trans
      (smooth_majorant hp)

lemma weighted_noise (hp : spec.valid p) :
    ∑ i, weights p i ^ 2 * (p.h i : ℝ) = information p :=
  InterpolationWeights.noise_identity p.L (fun i => (p.h i : ℝ)) (threshold p)
    (fun i => by exact_mod_cast hp.1 i)

end LongTails.Proofs.WeakInterpolationDesign
