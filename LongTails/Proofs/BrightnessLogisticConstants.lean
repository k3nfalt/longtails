import LongTails.Setups.BrightnessLogisticJoint
import Mathlib.Tactic

open LongTails.Setups.BrightnessLogisticJoint

namespace LongTails.Proofs.BrightnessLogisticConstants

lemma log_bound (p : Params) : 1 ≤ p.L := by
  have hn : (1:ℝ) ≤ p.n := by exact_mod_cast p.n.property
  exact le_add_of_nonneg_right (Real.log_nonneg (by linarith))

lemma horizon (p : Params) (hp : Valid p) : 1 ≤ p.M := by
  have h1 := log_bound p
  have hγ := hp.marginPos
  have hg := hp.floorPos
  unfold Params.M
  apply le_trans (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_right _)
  positivity

lemma initial_energy (p : Params) (_hp : Valid p) :
    1 ≤ 1+3*(p.p₀^2+p.t^2)+p.q₀^2+‖p.w‖^2 := by
  nlinarith [sq_nonneg p.p₀,sq_nonneg p.t,sq_nonneg p.q₀,sq_nonneg ‖p.w‖]

lemma energy_bound (p : Params) (hp : Valid p) : 1 ≤ p.B := by
  have hL := log_bound p
  have hM := horizon p hp
  have hJ := hp.forcePos
  have h : 0 ≤ (6*p.L+22*p.J+5*p.J^2)*(p.M+1) := by positivity
  exact one_le_mul_of_one_le_of_one_le (initial_energy p hp) (Real.one_le_exp h)

lemma dc_nonneg (p : Params) (hp : Valid p) : 0 ≤ p.D := (abs_nonneg _).trans (hp.maxDC 0)

lemma step_scale (p : Params) (hp : Valid p) : 0 < p.κ ∧ p.κ ≤ 1 := by
  have hD := dc_nonneg p hp
  have hJ := hp.forcePos
  have hB := energy_bound p hp
  have hd : 0 < 4*(1+p.D)*(1+p.J*p.B) := by positivity
  unfold Params.κ
  refine ⟨one_div_pos.mpr hd,(div_le_iff₀ hd).mpr ?_⟩
  nlinarith only [mul_nonneg (by linarith : 0 ≤ p.J) (by linarith : 0 ≤ p.B),
    mul_nonneg hD (mul_nonneg (by linarith : 0 ≤ p.J) (by linarith : 0 ≤ p.B)),hD]

lemma step_size (p : Params) (hp : Valid p) : 0 < p.κ/p.R ∧ p.κ/p.R ≤ 1 := by
  have hs := step_scale p hp
  have hR : 0 < p.R := zero_lt_one.trans_le hp.scale
  exact ⟨div_pos hs.1 hR,(div_le_iff₀ hR).mpr (by linarith [hp.scale])⟩

lemma radius_pos (p : Params) (hp : Valid p) : 0 < p.δ := by
  have hB := energy_bound p hp
  have hJ := hp.forcePos
  have hM := horizon p hp
  unfold Params.δ
  positivity

lemma collision (p : Params) (hp : Valid p) :
    p.γ*p.g*p.M > ‖p.a‖+
      Real.sqrt (p.p₀^2+p.q₀^2+2*p.t^2+3+(3*p.L+1)*(p.M+1)) := by
  let K := 3*p.L+1
  let C := p.p₀^2+p.q₀^2+2*p.t^2+3+K
  let ν := p.γ*p.g
  have hν : 0 < ν := mul_pos hp.marginPos hp.floorPos
  have hL := log_bound p
  have hK : 0 < K := by dsimp [K]; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hM := horizon p hp
  have hm' : p.M = 1+2*(‖p.a‖+Real.sqrt C)/ν+4*K/ν^2 := rfl
  have he : ν*p.M = ν+2*(‖p.a‖+Real.sqrt C)+4*K/ν := by
    rw [hm']
    field_simp [hν.ne']
  have hleft : 2*(‖p.a‖+Real.sqrt C) < ν*p.M := by
    linarith [div_pos (by positivity : 0 < 4*K) hν]
  have hquad : 4*K < ν^2*p.M := by
    have hδ := div_nonneg (by positivity : 0 ≤ 2*(‖p.a‖+Real.sqrt C)) hν.le
    have hlt : 4*K/ν^2 < p.M := by rw [hm']; linarith
    nlinarith only [(div_lt_iff₀ (sq_pos_of_pos hν)).mp hlt]
  have hright : 2*Real.sqrt (K*p.M) < ν*p.M := by
    have hmpos := zero_lt_one.trans_le hM
    have hsq := mul_lt_mul_of_pos_right hquad hmpos
    have hprod := mul_pos hν hmpos
    by_contra! hn
    have hs := mul_self_le_mul_self hprod.le hn
    nlinarith only [hs,hsq,Real.sq_sqrt (mul_nonneg hK.le hmpos.le)]
  have hsum : Real.sqrt (C+K*p.M) ≤ Real.sqrt C+Real.sqrt (K*p.M) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith [Real.sq_sqrt hC,Real.sq_sqrt (mul_nonneg hK.le (zero_le_one.trans hM)),
      mul_nonneg (Real.sqrt_nonneg C) (Real.sqrt_nonneg (K*p.M))]
  rw [show p.p₀^2+p.q₀^2+2*p.t^2+3+(3*p.L+1)*(p.M+1)=C+K*p.M by dsimp [C,K]; ring]
  change ‖p.a‖+Real.sqrt (C+K*p.M)<ν*p.M
  linarith

end LongTails.Proofs.BrightnessLogisticConstants
