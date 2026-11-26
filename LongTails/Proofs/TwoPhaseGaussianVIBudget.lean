import LongTails.Proofs.TwoPhaseGaussianVIStep

open MeasureTheory
namespace OracleTemplate.GaussianVariational.TwoPhaseGaussianVI
open LongTails.Setups.GaussianVariationalInference
variable {d : ℕ} {L μ : ℝ} {V : Point d → ℝ}

lemma startup_decay {μ ε R a η : ℝ} (hm : 0 < μ) (he : 0 < ε) (ha : 2 ≤ a)
    (hid : η*(μ*a) = 2) {T : ℕ}
    (hT : a/2 * Real.log (max 1 (μ*R^2/ε)) ≤ T) :
    (1-η*μ)^T * R^2 ≤ ε/μ := by
  let M := max 1 (μ*R^2/ε)
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left ..)
  have ha' : 0 < a := by linarith
  have hid' : η*μ = 2/a := (eq_div_iff ha'.ne').mpr (by linarith only [hid])
  rw [hid']
  have hp : 0 ≤ 1 - 2/a := sub_nonneg.mpr ((div_le_one ha').mpr ha)
  have hexp : 1-2/a ≤ Real.exp (-(2/a)) := by linarith [Real.add_one_le_exp (-(2/a))]
  have hpow := pow_le_pow_left₀ hp hexp T
  rw [← Real.exp_nat_mul] at hpow
  have ht : (T:ℝ) * (-(2/a)) ≤ -Real.log M := by
    have hh : a/2*Real.log M ≤ T := hT
    have := mul_le_mul_of_nonneg_right hh (show 0 ≤ 2/a by positivity)
    have e : a/2*Real.log M*(2/a) = Real.log M := by field_simp
    linarith
  have hh := hpow.trans (Real.exp_le_exp.mpr ht)
  rw [Real.exp_neg, Real.exp_log hM] at hh
  refine (mul_le_mul_of_nonneg_right hh (sq_nonneg R)).trans ?_
  rw [inv_mul_eq_div, div_le_div_iff₀ hM hm]
  have := (div_le_iff₀ he).mp (le_max_right 1 (μ*R^2/ε))
  linarith

lemma phase_budget (h : Potential L μ V) {ms : Location d} {Cs : Scale d}
    (ho : IsOptimal V ms Cs) {z : Location d × Scale d} (hz : IsCholesky z.2)
    {ε R : ℝ} (he : 0 < ε) (hr : sqd z (ms,Cs) ≤ R^2) {K T : ℕ}
    (hT : offset L μ d/2 * Real.log (max 1 (μ*R^2/ε)) ≤ T)
    (hK : 2*offset L μ d*(1+d/ε) ≤ K) :
    let a := offset L μ d
    let η := stepSize μ a 0
    let Q := energy V ms Cs η z
    let W := wmass a 0 K
    2/W*(μ/4*a^2)*((1-η*μ)^T*(Q-d/(2*μ))+d/(2*μ))+
      2/W*(4*K*noiseConst L μ d/μ) ≤ ε := by
  intro a η Q W
  have hc := constants h
  have hm := h.pos
  have ha : 2 ≤ a := hc.offset_ge
  have hη : 0 < η := hc.step_pos
  have iden : η*(μ*a) = 2 := hc.identity
  have hd := Nat.cast_nonneg (α := ℝ) d
  have kk : 2*a*(1+d/ε) ≤ K := hK
  have k1 : 2*a ≤ K := by
    nlinarith [mul_nonneg (show 0 ≤ a by linarith) (div_nonneg hd he.le)]
  have kpos : (0:ℝ) < K := by linarith
  have Wpos : 0 < W := wmass_pos ha 0 (by exact_mod_cast kpos)
  have Wge : (K:ℝ)^2/2 ≤ W := wmass_ge ha K
  have dupper := bregmanMean_upper h (ms := ms) (Cs := Cs) z.1 (isLower_sub hz.1 ho.1.1)
  change bregmanMean V ms Cs z.1 z.2 ≤ L/2*sqd z (ms,Cs) at dupper
  have qle : Q ≤ 2*R^2 := by
    dsimp only [Q,energy]
    have hs : η*L ≤ 1 := hc.smooth
    nlinarith [mul_le_mul_of_nonneg_left dupper hη.le,
      mul_le_mul_of_nonneg_right hs (sqd_nonneg z (ms,Cs))]
  have ρpos : 0 ≤ 1-η*μ := by
    nlinarith [mul_nonneg (mul_nonneg hη.le hm.le) (show 0 ≤ a-2 by linarith)]
  have decay := startup_decay hm he ha iden hT
  have s : (1-η*μ)^T*(Q-d/(2*μ))+d/(2*μ) ≤ (2*ε+d/2)/μ := by
    have hq : Q-d/(2*μ) ≤ 2*R^2 := by linarith [show 0 ≤ (d:ℝ)/(2*μ) by positivity]
    have := mul_le_mul_of_nonneg_left hq (pow_nonneg ρpos T)
    have eqn : (2*ε+d/2)/μ = 2*(ε/μ)+d/(2*μ) := by ring
    linarith
  have mass : 2*a*(ε+d) ≤ (K:ℝ)*ε := by
    have := mul_le_mul_of_nonneg_right kk he.le
    have eqn : 2*a*(1+d/ε)*ε = 2*a*(ε+d) := by field_simp
    linarith
  have sqmass : 4*a^2*(ε+d) ≤ (K:ℝ)^2*ε := by
    have := mul_le_mul k1 mass (show 0 ≤ 2*a*(ε+d) by positivity) (Nat.cast_nonneg K)
    linarith only [this]
  have da : 16*smoothConst L μ d/μ+2 = a := rfl
  have noise : 32*noiseConst L μ d/μ ≤ (K:ℝ)*ε := by
    have en : 32*noiseConst L μ d/μ = 2*(a-2)*d := by
      rw [← da]; unfold noiseConst smoothConst; ring
    rw [en]
    nlinarith [mul_nonneg (show 0 ≤ a by linarith) he.le]
  have t1 : μ/4*a^2*((1-η*μ)^T*(Q-d/(2*μ))+d/(2*μ)) ≤ (K:ℝ)^2*ε/8 := by
    have := mul_le_mul_of_nonneg_left s (show 0 ≤ μ/4*a^2 by positivity)
    have eqn : μ/4*a^2*((2*ε+d/2)/μ) = a^2*(2*ε+d/2)/4 := by field_simp
    nlinarith [mul_nonneg (sq_nonneg a) hd]
  have t2 : 4*K*noiseConst L μ d/μ ≤ (K:ℝ)^2*ε/8 := by
    calc _ = (K:ℝ)*(32*noiseConst L μ d/μ)/8 := by ring
         _ ≤ (K:ℝ)*((K:ℝ)*ε)/8 := by gcongr
         _ = _ := by ring
  have t3 := mul_le_mul_of_nonneg_right Wge he.le
  rw [mul_assoc, ← mul_add, div_mul_eq_mul_div, div_le_iff₀ Wpos]
  linarith only [t1,t2,t3]

end OracleTemplate.GaussianVariational.TwoPhaseGaussianVI
