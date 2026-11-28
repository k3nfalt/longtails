import LongTails.Proofs.BrightnessPrefixLength
import LongTails.Proofs.BrightnessTerminalLength

namespace LongTails.Proofs.BrightnessFirstFitConvergence

open LongTails.Setups.BrightnessScaledTwoTap
open BrightnessFirstFitParameters
open BrightnessScaledCoordinates
open BrightnessStiffPhase

lemma hit (p : Params) (x : Images p) (valid : spec.valid p) (G : Geometry p x) :
    ∃ k ≤ (scales p).H, Fitted p x (physical p (path p x (scales p).κ k)) := by
  classical
  by_contra! nonfit
  let c := scales p
  let S := path p x c.κ
  have h : Tuning p c := tuning p valid
  let after (k : ℕ) := pole p x c k ≤ c.V*c.M/p.R ∨ c.V*c.M < ‖(S k).w‖
  have pre (k : ℕ) (hh : ¬ after k) : c.V*c.M/p.R < pole p x c k ∧ ‖(S k).w‖ ≤ c.V*c.M :=
    ⟨lt_of_not_ge (fun ha => hh (Or.inl ha)),le_of_not_gt (fun ha => hh (Or.inr ha))⟩
  have n : 0 < (p.n : ℝ) := by exact_mod_cast p.n.property
  have V : 0 < c.V := by linarith only [h.Vge]
  have M := h.Mpos
  have K := h.κpos
  have Γ := h.Γpos
  have hb := (div_le_iff₀ (mul_pos K Γ)).mp h.budget
  have hh : 0 < (p.n:ℝ)*c.V^2*c.M := by positivity
  by_cases he : ∃ k, k ≤ c.H ∧ after k
  · let j := Nat.find he
    obtain ⟨hj,hafter⟩ := Nat.find_spec he
    have hpfx := BrightnessPrefixLength.prefix_bound p x valid G j hj
      (fun k hk => pre k (fun H => (Nat.find_min he hk) ⟨hk.le.trans hj,H⟩))
      (fun k hk => nonfit k (hk.le.trans hj))
    have hfloor := hafter.resolve_right (not_lt_of_ge hpfx.1)
    have dend := BrightnessTerminalLength.terminal p x valid G j hj ⟨hfloor,hpfx.1⟩
      (fun k hk => nonfit k hk.le)
    have hf := hpfx.2
    have hV' := mul_le_mul_of_nonneg_right h.Vge V.le
    nlinarith only [hf,dend,hb,hh,mul_le_mul_of_nonneg_right hV'
      (mul_nonneg n.le M.le)]
  · have hpfx := BrightnessPrefixLength.prefix_bound p x valid G c.H le_rfl
      (fun k hk => pre k (fun H => he ⟨k,hk.le,H⟩)) (fun k hk => nonfit k hk.le)
    nlinarith only [hpfx.2,hb,hh]

end LongTails.Proofs.BrightnessFirstFitConvergence
