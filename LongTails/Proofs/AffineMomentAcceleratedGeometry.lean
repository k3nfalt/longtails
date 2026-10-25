import LongTails.Algorithms.AffineMomentAccelerated
import LongTails.Proofs.FiniteMomentMirrorGeometry

open scoped RealInnerProductSpace
open LongTails.Algorithms.AffineMomentAccelerated

namespace LongTails.Proofs.AffineMomentAcceleratedGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def energy (u z : E) : ℝ := ‖z - u‖ ^ 2 / 2

omit [InnerProductSpace ℝ E] in
lemma energy_nonneg (u z : E) : 0 ≤ energy u z := by unfold energy; positivity

omit [InnerProductSpace ℝ E] in
lemma energy_le_two (u z : E) (hu : ‖u‖ ≤ 1) (hz : ‖z‖ ≤ 1) : energy u z ≤ 2 := by
  have hn : ‖z - u‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  unfold energy
  nlinarith [norm_nonneg (z - u)]

omit [InnerProductSpace ℝ E] in
lemma energy_lipschitz (u z w : E) (hu : ‖u‖ ≤ 1) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |energy u w - energy u z| ≤ 2 * ‖w - z‖ := by
  have hnw : ‖w - u‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have hnz : ‖z - u‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have hd := abs_norm_sub_norm_le (w - u) (z - u)
  rw [show (w - u) - (z - u) = w - z by abel] at hd
  have hs : ‖w - u‖ + ‖z - u‖ ≤ 4 := by linarith
  have hm := mul_le_mul hd hs (by positivity : 0 ≤ ‖w - u‖ + ‖z - u‖) (norm_nonneg (w - z))
  unfold energy
  rw [show ‖w - u‖ ^ 2 / 2 - ‖z - u‖ ^ 2 / 2 =
    (‖w - u‖ - ‖z - u‖) * (‖w - u‖ + ‖z - u‖) / 2 by ring,
    abs_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖w - u‖ + ‖z - u‖)]
  norm_num
  linarith

lemma mirror_displacement {a : ℝ} (ha : 0 ≤ a) (z g : E) (hz : ‖z‖ ≤ 1) :
    ‖mirrorStep a z g - z‖ ≤ a * ‖g‖ := by
  have h := OracleTemplate.norm_clip_sub_le (by norm_num : (0 : ℝ) ≤ 1) hz (z - a • g)
  simpa [mirrorStep, sub_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha] using h

lemma mirror_quadratic {a : ℝ} (ha : 0 ≤ a) (u z g : E) (hu : ‖u‖ ≤ 1) :
    energy u (mirrorStep a z g) ≤ energy u z - a * inner ℝ g (z - u) +
      (a * ‖g‖) ^ 2 / 2 := by
  have hn := OracleTemplate.norm_clip_sub_le (by norm_num : (0 : ℝ) ≤ 1) hu (z - a • g)
  have hs := sq_le_sq₀ (norm_nonneg (OracleTemplate.clip 1 (z - a • g) - u))
    (norm_nonneg (z - a • g - u))
  have ht := hs.mpr hn
  rw [show z - a • g - u = (z - u) - a • g by abel, norm_sub_sq_real (z - u) (a • g),
    norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, inner_smul_right] at ht
  rw [real_inner_comm g (z - u)] at ht
  unfold energy mirrorStep
  nlinarith only [ht]

lemma mirror_linear {a : ℝ} (ha : 0 ≤ a) (u z g : E) (hu : ‖u‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    energy u (mirrorStep a z g) ≤ energy u z - a * inner ℝ g (z - u) + 4 * a * ‖g‖ := by
  have hw : ‖mirrorStep a z g‖ ≤ 1 := OracleTemplate.norm_clip_le (by norm_num) _
  have hd := (le_abs_self _).trans (energy_lipschitz u z (mirrorStep a z g) hu hz hw)
  have hm := mirror_displacement ha z g hz
  have hn : ‖z - u‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have hi := real_inner_le_norm g (z - u)
  have hi' := mul_le_mul_of_nonneg_left hi ha
  have hn' := mul_le_mul_of_nonneg_left hn (show 0 ≤ a * ‖g‖ by positivity)
  nlinarith only [hd, hm, hi', hn']

lemma mirror_power {p a : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (ha : 0 ≤ a)
    (u z g : E) (hu : ‖u‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    energy u (mirrorStep a z g) ≤ energy u z - a * inner ℝ g (z - u) +
      4 * a ^ p * ‖g‖ ^ p := by
  have ht : 0 ≤ a * ‖g‖ := by positivity
  rw [show 4 * a ^ p * ‖g‖ ^ p = 4 * (a * ‖g‖) ^ p by
    rw [Real.mul_rpow ha (norm_nonneg g)]; ring]
  by_cases hsmall : a * ‖g‖ ≤ 1
  · have hs := Real.rpow_le_rpow_of_exponent_ge' ht hsmall (by linarith : 0 ≤ p) hp2
    rw [Real.rpow_two] at hs
    have hd := mirror_quadratic ha u z g hu
    nlinarith [Real.rpow_nonneg ht p]
  · have hs := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hsmall) hp
    rw [Real.rpow_one] at hs
    have hd := mirror_linear ha u z g hu hz
    nlinarith only [hs, hd]

lemma mirror_energy_square {p a : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (ha : 0 ≤ a)
    (u z g : E) (hu : ‖u‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    (energy u (mirrorStep a z g) - energy u z) ^ 2 ≤ 4 * a ^ p * ‖g‖ ^ p := by
  have hw : ‖mirrorStep a z g‖ ≤ 1 := OracleTemplate.norm_clip_le (by norm_num) _
  have hd := energy_lipschitz u z (mirrorStep a z g) hu hz hw
  have hm := mirror_displacement ha z g hz
  have hsmall : |energy u (mirrorStep a z g) - energy u z| ≤ 2 * (a * ‖g‖) := by
    linarith
  have hbound : |energy u (mirrorStep a z g) - energy u z| ≤ 2 := by
    rw [abs_le]
    have h1 := energy_nonneg u z
    have h2 := energy_nonneg u (mirrorStep a z g)
    have h3 := energy_le_two u z hu hz
    have h4 := energy_le_two u (mirrorStep a z g) hu hw
    constructor <;> linarith
  have ht : 0 ≤ a * ‖g‖ := by positivity
  rw [show 4 * a ^ p * ‖g‖ ^ p = 4 * (a * ‖g‖) ^ p by
    rw [Real.mul_rpow ha (norm_nonneg g)]; ring]
  by_cases hc : a * ‖g‖ ≤ 1
  · have hs := Real.rpow_le_rpow_of_exponent_ge' ht hc (by linarith : 0 ≤ p) hp2
    rw [Real.rpow_two] at hs
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hsmall 2
    rw [sq_abs] at hsq
    nlinarith only [hsq, hs]
  · have hs := Real.one_le_rpow (le_of_not_ge hc) (by linarith : 0 ≤ p)
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hbound 2
    rw [sq_abs] at hsq
    nlinarith only [hsq, hs]

end LongTails.Proofs.AffineMomentAcceleratedGeometry
