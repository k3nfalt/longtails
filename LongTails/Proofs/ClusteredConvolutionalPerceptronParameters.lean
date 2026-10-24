import LongTails.Proofs.ClusteredConvolutionalPerceptronDynamics

namespace LongTails.Proofs.ClusteredConvolutionalPerceptronParameters

open ClusteredConvolutionalPerceptronDynamics

lemma delta_le_one {κ ρ δ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 4)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hsmall : δ ≤ κ ^ 2 * ρ ^ 8 / 4096) : δ ≤ 1 := by
  have hk2 : κ ^ 2 ≤ 1 := by nlinarith
  have hr8 : ρ ^ 8 ≤ 1 := pow_le_one₀ hρ.le hρ1
  have hm := mul_le_mul hk2 hr8 (pow_nonneg hρ.le 8) (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith

noncomputable def control (κ ρ δ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 4)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 < δ)
    (hsmall : δ ≤ κ ^ 2 * ρ ^ 8 / 4096) : Control where
  C := κ / 8
  e := κ / 8
  g := κ ^ 2
  h := κ ^ 2 / 2
  ρ := ρ
  δ := δ
  L := ρ ^ 4 / 32
  C_pos := by positivity
  e_nonneg := by positivity
  h_pos := by positivity
  rho_pos := hρ
  rho_le := hρ1
  delta_pos := hδ
  L_nonneg := by positivity
  signal := by nlinarith [sq_nonneg κ]
  lorentz_small := by
    have hd := delta_le_one hκ hκ1 hρ hρ1 hsmall
    have hk2 : κ ^ 2 ≤ 1 := by nlinarith
    have hm := mul_le_mul hd hk2 (sq_nonneg κ) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  forcing_small := by nlinarith [sq_nonneg κ, pow_nonneg hρ.le 8]
  cone_small := by
    have hr2 : ρ ^ 2 ≤ 1 := by nlinarith
    have hr4 : ρ ^ 4 ≤ ρ ^ 2 := by nlinarith [sq_nonneg (ρ ^ 2)]
    have hm := mul_le_mul_of_nonneg_left hr4 hκ.le
    nlinarith [mul_nonneg hκ.le (sq_nonneg ρ)]

lemma control_initial {κ ρ δ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 4)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 < δ)
    (hsmall : δ ≤ κ ^ 2 * ρ ^ 8 / 4096) :
    let c := control κ ρ δ hκ hκ1 hρ hρ1 hδ hsmall
    8 * c.C ^ 2 ≤ c.h := by
  dsimp [control]
  nlinarith [sq_nonneg κ]

lemma control_noise {κ ρ δ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 4)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 < δ)
    (hsmall : δ ≤ κ ^ 2 * ρ ^ 8 / 4096) :
    let c := control κ ρ δ hκ hκ1 hρ hρ1 hδ hsmall
    (12 * (c.C + c.e) / c.ρ ^ 2) ^ 2 * c.L ≤ c.h := by
  dsimp [control]
  have he : (12 * (κ / 8 + κ / 8) / ρ ^ 2) ^ 2 * (ρ ^ 4 / 32) =
      9 * κ ^ 2 / 32 := by field_simp [ne_of_gt hρ]; ring
  rw [he]
  nlinarith [sq_nonneg κ]

end LongTails.Proofs.ClusteredConvolutionalPerceptronParameters
