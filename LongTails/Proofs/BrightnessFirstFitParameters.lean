import LongTails.Setups.BrightnessScaledTwoTap
import Mathlib.Tactic

namespace LongTails.Proofs.BrightnessFirstFitParameters

open LongTails.Setups.BrightnessScaledTwoTap

structure Tuning (p : Params) (c : Scales) : Prop where
  μpos : 0 < p.μ
  γpos : 0 < p.γ
  Dpos : 0 < p.D
  Jpos : 0 < p.J
  Qne : p.Q ≠ 0
  Rlarge : 1 ≤ p.R
  Upos : 0 < c.U
  Ueq : c.U = p.J*(4+|p.P|+|p.Q|)
  Γpos : 0 < c.Γ
  Γle : c.Γ ≤ 1/4
  margin : 4*c.Γ ≤ |p.Q| * p.γ
  κpos : 0 < c.κ
  κeq : c.κ*(32*(1+p.D)*(1+c.U)) = c.Γ
  δpos : 0 < c.δ
  δeq : c.δ*(128*(1+p.J)) = c.Γ
  Vge : 6 ≤ c.V
  Veq : c.V = 6+Real.sqrt (Real.log (1+|p.P|/c.δ))
  fpos : 0 < c.f
  feq : c.f*(32*p.n*c.V*(1+c.U)) = p.μ*c.Γ
  Bge : 1 ≤ c.B
  Beq : c.B = 1+(1+Real.log (4*(1+|p.P|)^2*p.R^2))/(c.κ*c.f)^2
  Mpos : 0 < c.M
  Meq : c.M = 8*(1+‖p.readout‖+(1+c.U)/p.μ+(1+Real.log (2*p.n)+c.κ*c.U^2)/c.Γ)+c.κ*c.U*c.B
  budget : 32*p.n*c.V^2*c.M/(c.κ*c.Γ) ≤ c.H

lemma tuning (p : Params) (valid : spec.valid p) : Tuning p (scales p) := by
  obtain ⟨hμ,hγ,hD,hJ,hQ,hR,_⟩ := valid
  let c := scales p
  have hUeq : c.U = p.J*(4+|p.P|+|p.Q|) := rfl
  have hΓeq : c.Γ = min 1 (|p.Q| * p.γ)/4 := rfl
  have hκeq : c.κ = c.Γ/(32*(1+p.D)*(1+c.U)) := rfl
  have hδeq : c.δ = c.Γ/(128*(1+p.J)) := rfl
  have hVeq : c.V = 6+Real.sqrt (Real.log (1+|p.P|/c.δ)) := rfl
  have hfeq : c.f = p.μ*c.Γ/(32*p.n*c.V*(1+c.U)) := rfl
  have hBeq : c.B = 1+(1+Real.log (4*(1+|p.P|)^2*p.R^2))/(c.κ*c.f)^2 := rfl
  have hMeq : c.M = 8*(1+‖p.readout‖+(1+c.U)/p.μ+(1+Real.log (2*p.n)+c.κ*c.U^2)/c.Γ)+c.κ*c.U*c.B := rfl
  have hU : 0 < c.U := by rw [hUeq]; positivity
  have hpQ := abs_pos.mpr hQ
  have hΓ : 0 < c.Γ := by rw [hΓeq]; positivity
  have hκ : 0 < c.κ := by rw [hκeq]; positivity
  have hδ : 0 < c.δ := by rw [hδeq]; positivity
  have hV : 6 ≤ c.V := by rw [hVeq]; linarith [Real.sqrt_nonneg (Real.log (1+|p.P|/c.δ))]
  have hV' : 0 < c.V := by linarith only [hV]
  have hf : 0 < c.f := by rw [hfeq]; positivity
  have hn : (1:ℝ) ≤ p.n := by exact_mod_cast p.n.property
  have logn : 0 ≤ Real.log (2*(p.n:ℝ)) := Real.log_nonneg (by linarith only [hn])
  have harg : (1:ℝ) ≤ 4*(1+|p.P|)^2*p.R^2 := by
    calc
      _ ≤ 4*(1:ℝ)^2*1^2 := by norm_num
      _ ≤ _ := by gcongr; linarith [abs_nonneg p.P]
  have hB : 1 ≤ c.B := by rw [hBeq,le_add_iff_nonneg_right]; have := Real.log_nonneg harg; positivity
  have hB' : 0 < c.B := by linarith only [hB]
  have hM : 0 < c.M := by rw [hMeq]; positivity
  refine ⟨hμ,hγ,hD,hJ,hQ,hR,hU,hUeq,hΓ,?_,?_,hκ,?_,hδ,?_,hV,hVeq,hf,?_,hB,hBeq,hM,hMeq,
    Nat.le_ceil _⟩
  · rw [hΓeq]; linarith only [min_le_left 1 (|p.Q| * p.γ)]
  · rw [hΓeq]; linarith only [min_le_right 1 (|p.Q| * p.γ)]
  · rw [hκeq,div_mul_cancel₀ _ (by positivity)]
  · rw [hδeq,div_mul_cancel₀ _ (by positivity)]
  · rw [hfeq,div_mul_cancel₀ _ (by positivity)]


noncomputable def radius (p : Params) (c : Scales) := ‖p.readout‖+c.κ*c.U*c.H
noncomputable def error (p : Params) (c : Scales) := c.κ*p.J*radius p c/p.R^2
noncomputable def growth (p : Params) (c : Scales) :=
  3*c.κ*(1+c.U*radius p c)/p.R^2+(4*(2+|p.P|)+1)*error p c

lemma small_tunings {p : Params} {c : Scales} (h : Tuning p c) :
    32*(c.κ*p.D)*(1+c.U) ≤ c.Γ ∧ 128*c.δ*(1+p.J) = c.Γ ∧
    c.δ ≤ 1 ∧ c.f ≤ p.μ/2 := by
  have H := h.κeq
  have H' := h.δeq
  have K : 0 < 32*c.κ*(1+c.U) := by have := h.κpos; have := h.Upos; positivity
  have Hf := h.feq
  have hn : (1:ℝ) ≤ p.n := by exact_mod_cast p.n.property
  have hcoeff : 2 ≤ 32*(p.n:ℝ)*c.V*(1+c.U) := by
    calc
      _ ≤ 32*1*6*(1+(0:ℝ)) := by norm_num
      _ ≤ _ := by
        have hu := h.Upos
        have hv : 0 ≤ c.V := by linarith only [h.Vge]
        gcongr
        exact h.Vge
  have hfμ := mul_le_mul_of_nonneg_left h.Γle h.μpos.le
  refine ⟨by nlinarith only [H,K],by nlinarith only [H'],?_,?_⟩
  · nlinarith only [H',h.Γle,h.δpos,mul_nonneg h.δpos.le h.Jpos.le]
  · nlinarith only [Hf,hfμ,h.μpos,mul_le_mul_of_nonneg_left hcoeff h.fpos.le]

lemma comparator_size {p : Params} {c : Scales} (h : Tuning p c) :
    1+‖p.readout‖+c.κ*c.U*c.B ≤ c.M ∧
    8*(1+c.U) ≤ c.M*p.μ ∧
    8*(1+Real.log (2*p.n)+c.κ*c.U^2) ≤ c.M*c.Γ := by
  have hn : (1:ℝ) ≤ p.n := by exact_mod_cast p.n.property
  have hL : 0 ≤ Real.log (2*(p.n:ℝ)) := Real.log_nonneg (by linarith only [hn])
  have κ := h.κpos
  have U := h.Upos
  have Γ := h.Γpos
  have μ := h.μpos
  have B : 0 ≤ c.B := by linarith only [h.Bge]
  have x : 0 ≤ (1+c.U)/p.μ := by positivity
  have y : 0 ≤ (1+Real.log (2*(p.n:ℝ))+c.κ*c.U^2)/c.Γ := by positivity
  have C : 0 ≤ c.κ*c.U*c.B := by positivity
  refine ⟨by linarith only [h.Meq,norm_nonneg p.readout,x,y],?_,?_⟩
  · apply (div_le_iff₀ μ).mp
    rw [mul_div_assoc]
    linarith only [h.Meq,norm_nonneg p.readout,C,y]
  · apply (div_le_iff₀ Γ).mp
    rw [mul_div_assoc]
    linarith only [h.Meq,norm_nonneg p.readout,C,x]

lemma scale_remainders (p : Params) (h : spec.valid p) :
    let c := scales p
    c.H*error p c ≤ c.δ/4 ∧ 16*c.H*error p c*p.R ≤ c.V*c.M ∧
      (‖p.readout‖/p.R^2)^2 + c.H*growth p c +
        2*(1+c.U*radius p c)/(p.μ*p.R^2)+(c.V*c.M/p.R)^2 ≤ c.δ^2 := h.2.2.2.2.2.2

end LongTails.Proofs.BrightnessFirstFitParameters
