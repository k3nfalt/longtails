import LongTails.Proofs.AdaptiveRobustGeneralizedConvergence

namespace OracleTemplate.AdaptiveRobustGeneralized

lemma inflate_valid (p : Params) (hp : spec.valid p) : spec.valid (inflate p) := by
  rcases hp with ⟨hL0, hL1, hR, hΔ, hσ, hε, hδ, hδ1⟩
  refine ⟨?_, hL1, hR, hΔ, hσ, hε, hδ, hδ1⟩
  change 0 < p.L0+(confidence p)^2*p.σ^2/p.ε
  have : 0 ≤ (confidence p)^2*p.σ^2/p.ε := by positivity
  linarith

lemma inflate_smooth (p : Params) (hε : 0 < p.ε) {f : p.E → ℝ}
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0+p.L1*‖gradient f x‖) :
    ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ (inflate p).L0+(inflate p).L1*‖gradient f x‖ := by
  intro x
  have h := hH x
  change _ ≤ (p.L0+(confidence p)^2*p.σ^2/p.ε)+p.L1*‖gradient f x‖
  have : 0 ≤ (confidence p)^2*p.σ^2/p.ε := by positivity
  linarith

lemma inflate_curvature (p : Params) :
    (inflate p).L0*(inflate p).R^2/(inflate p).ε = (p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2)) := by
  change (p.L0+(confidence p)^2*p.σ^2/p.ε)*p.R^2/p.ε = _
  unfold confidence
  by_cases hε : p.ε = 0
  · simp [hε]
  · field_simp

lemma budget_algebra {W V ℓ H S : ℝ} (hW : 1 ≤ W) (hV : 0 ≤ V) (hH : 1 ≤ H)
    (hS : 1 ≤ S) :
    116*(16385*W)+1099511627776*V*ℓ+156*H*(1099511627776*V*ℓ^2/S)+
      112*H*(16385*W)/Real.log (Real.exp 1+16385*W/(1099511627776*V*ℓ^2/S+16385*W*Real.exp (-28*H))) ≤
    2^21*W+2^40*V*ℓ+2^48*H*V*ℓ^2/S+
      2^21*H*W/Real.log (Real.exp 1+W*S/(2^26*V*ℓ^2+W*S*Real.exp (-28*H))) := by
  have he : 0 < Real.exp (-28*H) := Real.exp_pos _
  have hS0 : 0 < S := by linarith
  have harg : W*S/(2^26*V*ℓ^2+W*S*Real.exp (-28*H)) ≤
      16385*W/(1099511627776*V*ℓ^2/S+16385*W*Real.exp (-28*H)) := by
    have hpos1 : 0 < 2^26*V*ℓ^2+W*S*Real.exp (-28*H) := by positivity
    have hpos2 : 0 < 1099511627776*V*ℓ^2/S+16385*W*Real.exp (-28*H) := by positivity
    rw [div_le_div_iff₀ hpos1 hpos2]
    have hx : W*S*(1099511627776*V*ℓ^2/S+16385*W*Real.exp (-28*H)) =
        W*(1099511627776*V*ℓ^2)+16385*W*(W*S*Real.exp (-28*H)) := by
      field_simp
    rw [hx]
    have hv : 0 ≤ W*(V*ℓ^2) := by positivity
    nlinarith
  have hlogpos : 0 < Real.log (Real.exp 1+W*S/(2^26*V*ℓ^2+W*S*Real.exp (-28*H))) :=
    Real.log_pos (by
      have h1 := Real.exp_one_gt_d9
      have h2 : 0 ≤ W*S/(2^26*V*ℓ^2+W*S*Real.exp (-28*H)) := by positivity
      linarith)
  have hlog : Real.log (Real.exp 1+W*S/(2^26*V*ℓ^2+W*S*Real.exp (-28*H))) ≤
      Real.log (Real.exp 1+16385*W/(1099511627776*V*ℓ^2/S+16385*W*Real.exp (-28*H))) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlast : 112*H*(16385*W)/Real.log (Real.exp 1+16385*W/(1099511627776*V*ℓ^2/S+16385*W*Real.exp (-28*H))) ≤
      2^21*H*W/Real.log (Real.exp 1+W*S/(2^26*V*ℓ^2+W*S*Real.exp (-28*H))) := by
    calc _ ≤ 112*H*(16385*W)/Real.log (Real.exp 1+W*S/(2^26*V*ℓ^2+W*S*Real.exp (-28*H))) :=
          div_le_div_of_nonneg_left (by positivity) hlogpos hlog
      _ ≤ _ := by
          apply div_le_div_of_nonneg_right _ hlogpos.le
          nlinarith [mul_nonneg (show 0 ≤ H by linarith) (show 0 ≤ W by linarith)]
  have hmid : 156*H*(1099511627776*V*ℓ^2/S) ≤ 2^48*H*V*ℓ^2/S := by
    have : 0 ≤ H*(V*ℓ^2/S) := by positivity
    have e1 : 156*H*(1099511627776*V*ℓ^2/S) = 171523813933056*(H*(V*ℓ^2/S)) := by ring
    have e2 : 2^48*H*V*ℓ^2/S = 281474976710656*(H*(V*ℓ^2/S)) := by ring
    rw [e1, e2]
    nlinarith
  have hfirst : 116*(16385*W) ≤ 2^21*W := by nlinarith
  have hcorr : 1099511627776*V*ℓ = 2^40*V*ℓ := by norm_num
  linarith

lemma public_budget_ge (p : Params) (hp : spec.valid p) :
    callBound (inflate p) ≤ (⌈2^21*(1+Real.sqrt (p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2))+Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))+2^40*(p.σ^2*p.R^2/p.ε^2)*Real.log (Real.exp 1/p.δ)+2^48*Real.log (Real.exp 1*(1+(p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2))+p.L1*p.R+Real.log (4+4*p.Δ/p.ε))/p.δ)*(p.σ^2*p.R^2/p.ε^2)*Real.log (Real.exp 1/p.δ)^2/Real.sqrt (1+(p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2)))+2^21*Real.log (Real.exp 1*(1+(p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2))+p.L1*p.R+Real.log (4+4*p.Δ/p.ε))/p.δ)*(1+Real.sqrt (p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2))+Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))/Real.log (Real.exp 1+(1+Real.sqrt (p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2))+Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))*Real.sqrt (1+(p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2)))/(2^26*(p.σ^2*p.R^2/p.ε^2)*Real.log (Real.exp 1/p.δ)^2+(1+Real.sqrt (p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2))+Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))*Real.sqrt (1+(p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2)))*Real.exp (-28*Real.log (Real.exp 1*(1+(p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2))+p.L1*p.R+Real.log (4+4*p.Δ/p.ε))/p.δ))))⌉₊ : ℝ) := by
  have hp' := inflate_valid p hp
  have hcurv := inflate_curvature p
  have hshape : shape (inflate p) = (1+Real.sqrt (p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2))+Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ)) := by
    unfold shape
    rw [hcurv]
    rfl
  have hlevel : level (inflate p) = Real.log (Real.exp 1*(1+(p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2))+p.L1*p.R+Real.log (4+4*p.Δ/p.ε))/p.δ) := by
    unfold level
    rw [hcurv]
    rfl
  have hroot : Real.sqrt (1+(inflate p).L0*(inflate p).R^2/(inflate p).ε) = Real.sqrt (1+(p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2))) := by
    rw [hcurv]
  have hW1 := shape_ge_one _ hp'
  have hH1 := level_ge_one _ hp'
  have hS1 : 1 ≤ Real.sqrt (1+(inflate p).L0*(inflate p).R^2/(inflate p).ε) := by
    have hε := hp'.2.2.2.2.2.1
    have hL0 := hp'.1
    have h0 : 0 ≤ (inflate p).L0*(inflate p).R^2/(inflate p).ε := by positivity
    have h1 : (1 : ℝ) ≤ 1+(inflate p).L0*(inflate p).R^2/(inflate p).ε := by linarith
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt h1
  have hℓ0 : 0 ≤ confidence (inflate p) :=
    (lt_trans zero_lt_one (StochasticGeneralized.confidence_log_gt_one
      hp'.2.2.2.2.2.2.1 hp'.2.2.2.2.2.2.2)).le
  have hV0 : 0 ≤ (inflate p).σ^2*(inflate p).R^2/(inflate p).ε^2 := by positivity
  have key := budget_algebra (ℓ := confidence (inflate p)) hW1 hV0 hH1 hS1
  have hcb : callBound (inflate p) =
      116*(16385*shape (inflate p))+1099511627776*((inflate p).σ^2*(inflate p).R^2/(inflate p).ε^2)*confidence (inflate p)+
        156*level (inflate p)*(1099511627776*((inflate p).σ^2*(inflate p).R^2/(inflate p).ε^2)*(confidence (inflate p))^2/
          Real.sqrt (1+(inflate p).L0*(inflate p).R^2/(inflate p).ε))+
        112*level (inflate p)*(16385*shape (inflate p))/Real.log (Real.exp 1+16385*shape (inflate p)/
          (1099511627776*((inflate p).σ^2*(inflate p).R^2/(inflate p).ε^2)*(confidence (inflate p))^2/
            Real.sqrt (1+(inflate p).L0*(inflate p).R^2/(inflate p).ε)+
            16385*shape (inflate p)*Real.exp (-28*level (inflate p)))) := by
    unfold callBound iterationScale pilotMass
    rfl
  rw [hcb]
  refine key.trans ?_
  rw [hshape, hlevel, hroot]
  exact Nat.le_ceil _

end OracleTemplate.AdaptiveRobustGeneralized
